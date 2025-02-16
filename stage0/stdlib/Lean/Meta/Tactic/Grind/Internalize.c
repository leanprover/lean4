// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Internalize
// Imports: Init.Grind.Util Init.Grind.Lemmas Lean.Meta.LitValues Lean.Meta.Match.MatcherInfo Lean.Meta.Match.MatchEqsExt Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Canon Lean.Meta.Tactic.Grind.Beta Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Grind.Arith.Internalize
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__5;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__15;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3;
extern lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3;
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__4;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2;
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__1;
uint8_t l_Lean_Expr_isDIte(lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__4;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isCongruent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3;
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__2;
uint64_t l_Lean_Meta_Grind_congrHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__1___boxed(lean_object**);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__11;
lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__16;
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__3;
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Offset_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_setENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_EMatchTheorems_isErased(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1;
lean_object* l_Lean_Meta_Grind_propagateUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4;
lean_object* l_Lean_Meta_Grind_EMatchTheorems_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Meta_Grind_unfoldReducible___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5;
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_groundPattern_x3f(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__1;
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__2;
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__13;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4;
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(lean_object*, lean_object*, size_t, lean_object*);
static size_t l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__4;
lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Offset_Main_0__Lean_Meta_Grind_Arith_Offset_setUnsat___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__7;
lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__5;
static lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
uint8_t l_Lean_Expr_isIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheorem(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__2;
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__10;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkGroundPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3;
lean_object* l_Lean_Meta_Grind_registerParent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__3;
lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMorallyIff___boxed(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_object* l_Lean_Meta_Grind_mkENodeCore(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___boxed(lean_object**);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__1;
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__2;
lean_object* l_Lean_Meta_Grind_Origin_key(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_congrPlaceholderProof;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_HeadIndex_hash(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2;
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__18;
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__17;
lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__2;
static lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_fget(x_2, x_5);
lean_inc(x_11);
lean_inc(x_6);
x_12 = l_Lean_Meta_Grind_isCongruent(x_7, x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = 5;
x_9 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_10 = lean_usize_land(x_3, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_box(2);
x_13 = lean_array_get(x_12, x_6, x_11);
lean_dec(x_11);
lean_dec(x_6);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_17 = l_Lean_Meta_Grind_isCongruent(x_7, x_4, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_2);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_19);
x_21 = l_Lean_Meta_Grind_isCongruent(x_7, x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_2);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_23);
return x_2;
}
}
}
case 1:
{
lean_object* x_24; size_t x_25; 
lean_dec(x_7);
lean_free_object(x_2);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_usize_shift_right(x_3, x_8);
x_2 = x_24;
x_3 = x_25;
goto _start;
}
default: 
{
lean_object* x_27; 
lean_dec(x_7);
lean_free_object(x_2);
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = 5;
x_31 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_32 = lean_usize_land(x_3, x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_box(2);
x_35 = lean_array_get(x_34, x_28, x_33);
lean_dec(x_33);
lean_dec(x_28);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
lean_inc(x_36);
x_39 = l_Lean_Meta_Grind_isCongruent(x_29, x_4, x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
case 1:
{
lean_object* x_43; size_t x_44; 
lean_dec(x_29);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_usize_shift_right(x_3, x_30);
x_2 = x_43;
x_3 = x_44;
goto _start;
}
default: 
{
lean_object* x_46; 
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_1);
x_46 = lean_box(0);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(x_1, x_47, x_48, lean_box(0), x_49, x_4);
lean_dec(x_48);
lean_dec(x_47);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Meta_Grind_congrHash(x_4, x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(x_1, x_2, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_array_fget(x_3, x_6);
x_12 = lean_array_fget(x_4, x_6);
lean_inc(x_11);
x_13 = l_Lean_Meta_Grind_congrHash(x_8, x_11);
x_14 = lean_uint64_to_usize(x_13);
x_15 = 1;
x_16 = lean_usize_sub(x_2, x_15);
x_17 = 5;
x_18 = lean_usize_mul(x_17, x_16);
x_19 = lean_usize_shift_right(x_14, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
lean_inc(x_1);
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_7, x_19, x_2, x_11, x_12);
x_5 = lean_box(0);
x_6 = x_21;
x_7 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_array_push(x_6, x_4);
x_15 = lean_array_push(x_7, x_5);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_array_push(x_6, x_4);
x_17 = lean_array_push(x_7, x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_fget(x_6, x_3);
lean_inc(x_4);
x_20 = l_Lean_Meta_Grind_isCongruent(x_8, x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_3 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_array_fset(x_6, x_3, x_4);
x_28 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_29 = lean_array_fset(x_6, x_3, x_4);
x_30 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = 1;
x_11 = 5;
x_12 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_13 = lean_usize_land(x_3, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get_size(x_8);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_8, x_14);
x_18 = lean_box(0);
x_19 = lean_array_fset(x_8, x_14, x_18);
switch (lean_obj_tag(x_17)) {
case 0:
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_5);
x_23 = l_Lean_Meta_Grind_isCongruent(x_9, x_5, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_17);
x_24 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_21, x_22, x_5, x_6);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_fset(x_19, x_14, x_25);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 0, x_5);
x_27 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
lean_inc(x_28);
lean_inc(x_5);
x_30 = l_Lean_Meta_Grind_isCongruent(x_9, x_5, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_28, x_29, x_5, x_6);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_array_fset(x_19, x_14, x_32);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_33);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
x_35 = lean_array_fset(x_19, x_14, x_34);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
}
}
case 1:
{
uint8_t x_36; 
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_usize_shift_right(x_3, x_11);
x_39 = lean_usize_add(x_4, x_10);
x_40 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_37, x_38, x_39, x_5, x_6);
lean_ctor_set(x_17, 0, x_40);
x_41 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_usize_shift_right(x_3, x_11);
x_44 = lean_usize_add(x_4, x_10);
x_45 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_42, x_43, x_44, x_5, x_6);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_19, x_14, x_46);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_6);
x_49 = lean_array_fset(x_19, x_14, x_48);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_49);
return x_2;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = 1;
x_53 = 5;
x_54 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_55 = lean_usize_land(x_3, x_54);
x_56 = lean_usize_to_nat(x_55);
x_57 = lean_array_get_size(x_50);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_50);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_array_fget(x_50, x_56);
x_61 = lean_box(0);
x_62 = lean_array_fset(x_50, x_56, x_61);
switch (lean_obj_tag(x_60)) {
case 0:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_65 = x_60;
} else {
 lean_dec_ref(x_60);
 x_65 = lean_box(0);
}
lean_inc(x_63);
lean_inc(x_5);
x_66 = l_Lean_Meta_Grind_isCongruent(x_51, x_5, x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_67 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_63, x_64, x_5, x_6);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_array_fset(x_62, x_56, x_68);
lean_dec(x_56);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_64);
lean_dec(x_63);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_5);
lean_ctor_set(x_71, 1, x_6);
x_72 = lean_array_fset(x_62, x_56, x_71);
lean_dec(x_56);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_51);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_75 = x_60;
} else {
 lean_dec_ref(x_60);
 x_75 = lean_box(0);
}
x_76 = lean_usize_shift_right(x_3, x_53);
x_77 = lean_usize_add(x_4, x_52);
x_78 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_74, x_76, x_77, x_5, x_6);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_array_fset(x_62, x_56, x_79);
lean_dec(x_56);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
default: 
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_51);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_5);
lean_ctor_set(x_82, 1, x_6);
x_83 = lean_array_fset(x_62, x_56, x_82);
lean_dec(x_56);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_2);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; size_t x_88; uint8_t x_89; 
x_86 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_87 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(x_1, x_2, x_86, x_5, x_6);
x_88 = 7;
x_89 = lean_usize_dec_le(x_88, x_4);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_87);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_dec_lt(x_90, x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_96 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(x_1, x_4, x_93, x_94, lean_box(0), x_86, x_95);
lean_dec(x_94);
lean_dec(x_93);
return x_96;
}
else
{
lean_dec(x_1);
return x_87;
}
}
else
{
lean_dec(x_1);
return x_87;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; uint8_t x_103; 
x_97 = lean_ctor_get(x_2, 0);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_2);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_101 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(x_1, x_99, x_100, x_5, x_6);
x_102 = 7;
x_103 = lean_usize_dec_le(x_102, x_4);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_101);
x_105 = lean_unsigned_to_nat(4u);
x_106 = lean_nat_dec_lt(x_104, x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
lean_dec(x_101);
x_109 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_110 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(x_1, x_4, x_107, x_108, lean_box(0), x_100, x_109);
lean_dec(x_108);
lean_dec(x_107);
return x_110;
}
else
{
lean_dec(x_1);
return x_101;
}
}
else
{
lean_dec(x_1);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_3);
x_6 = l_Lean_Meta_Grind_congrHash(x_5, x_3);
x_7 = lean_uint64_to_usize(x_6);
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_2, x_7, x_8, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_45; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_Meta_Grind_hasSameType(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Meta_Grind_congrPlaceholderProof;
x_50 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_Meta_Grind_pushEqCore(x_1, x_2, x_49, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_13 = x_52;
goto block_44;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = l_Lean_Meta_Grind_congrPlaceholderProof;
x_55 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_56 = l_Lean_Meta_Grind_pushEqCore(x_1, x_2, x_54, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_13 = x_57;
goto block_44;
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_44:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Meta_Grind_Goal_getENode(x_15, x_1, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 3);
lean_dec(x_21);
lean_ctor_set(x_18, 3, x_2);
x_22 = l_Lean_Meta_Grind_setENode(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
x_25 = lean_ctor_get(x_18, 2);
x_26 = lean_ctor_get(x_18, 4);
x_27 = lean_ctor_get(x_18, 5);
x_28 = lean_ctor_get_uint8(x_18, sizeof(void*)*11);
x_29 = lean_ctor_get(x_18, 6);
x_30 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 1);
x_31 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 2);
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 3);
x_33 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 4);
x_34 = lean_ctor_get(x_18, 7);
x_35 = lean_ctor_get(x_18, 8);
x_36 = lean_ctor_get(x_18, 9);
x_37 = lean_ctor_get(x_18, 10);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_38 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_25);
lean_ctor_set(x_38, 3, x_2);
lean_ctor_set(x_38, 4, x_26);
lean_ctor_set(x_38, 5, x_27);
lean_ctor_set(x_38, 6, x_29);
lean_ctor_set(x_38, 7, x_34);
lean_ctor_set(x_38, 8, x_35);
lean_ctor_set(x_38, 9, x_36);
lean_ctor_set(x_38, 10, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*11, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 1, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 2, x_31);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 3, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 4, x_33);
x_39 = l_Lean_Meta_Grind_setENode(x_1, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2;
x_3 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4;
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_19 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_1);
x_25 = l_Lean_MessageData_ofExpr(x_1);
x_26 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_25);
lean_ctor_set(x_14, 0, x_26);
x_27 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_2);
x_29 = l_Lean_MessageData_ofExpr(x_2);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_13, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
lean_dec(x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_free_object(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_dec(x_14);
x_41 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_1);
x_43 = l_Lean_MessageData_ofExpr(x_1);
x_44 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_2);
x_48 = l_Lean_MessageData_ofExpr(x_2);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
x_51 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_13, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_57 = x_41;
} else {
 lean_dec_ref(x_41);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_addCongrTable___lambda__3___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found congruence between", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nand", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nbut functions have different types", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(x_13, x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_st_ref_take(x_2, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 6);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_18, sizeof(void*)*15);
x_28 = lean_ctor_get(x_18, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 8);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 9);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 10);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 11);
lean_inc(x_32);
x_33 = lean_ctor_get(x_18, 12);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 13);
lean_inc(x_34);
x_35 = lean_ctor_get(x_18, 14);
lean_inc(x_35);
x_36 = lean_box(0);
lean_inc(x_18);
x_37 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(x_18, x_24, x_1, x_36);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_39 = lean_ctor_get(x_18, 14);
lean_dec(x_39);
x_40 = lean_ctor_get(x_18, 13);
lean_dec(x_40);
x_41 = lean_ctor_get(x_18, 12);
lean_dec(x_41);
x_42 = lean_ctor_get(x_18, 11);
lean_dec(x_42);
x_43 = lean_ctor_get(x_18, 10);
lean_dec(x_43);
x_44 = lean_ctor_get(x_18, 9);
lean_dec(x_44);
x_45 = lean_ctor_get(x_18, 8);
lean_dec(x_45);
x_46 = lean_ctor_get(x_18, 7);
lean_dec(x_46);
x_47 = lean_ctor_get(x_18, 6);
lean_dec(x_47);
x_48 = lean_ctor_get(x_18, 5);
lean_dec(x_48);
x_49 = lean_ctor_get(x_18, 4);
lean_dec(x_49);
x_50 = lean_ctor_get(x_18, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_18, 2);
lean_dec(x_51);
x_52 = lean_ctor_get(x_18, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_18, 0);
lean_dec(x_53);
lean_ctor_set(x_18, 4, x_37);
x_54 = lean_st_ref_set(x_2, x_18, x_19);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_36);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_18);
x_59 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_59, 0, x_20);
lean_ctor_set(x_59, 1, x_21);
lean_ctor_set(x_59, 2, x_22);
lean_ctor_set(x_59, 3, x_23);
lean_ctor_set(x_59, 4, x_37);
lean_ctor_set(x_59, 5, x_25);
lean_ctor_set(x_59, 6, x_26);
lean_ctor_set(x_59, 7, x_28);
lean_ctor_set(x_59, 8, x_29);
lean_ctor_set(x_59, 9, x_30);
lean_ctor_set(x_59, 10, x_31);
lean_ctor_set(x_59, 11, x_32);
lean_ctor_set(x_59, 12, x_33);
lean_ctor_set(x_59, 13, x_34);
lean_ctor_set(x_59, 14, x_35);
lean_ctor_set_uint8(x_59, sizeof(void*)*15, x_27);
x_60 = lean_st_ref_set(x_2, x_59, x_19);
lean_dec(x_2);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_36);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_16, 0);
lean_inc(x_64);
lean_dec(x_16);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_dec(x_67);
x_68 = l_Lean_Expr_getAppFn(x_1);
x_69 = l_Lean_Expr_getAppFn(x_66);
x_70 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_71 = l_Lean_Meta_Grind_hasSameType(x_68, x_69, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lean_Meta_Grind_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = l_Lean_Meta_Grind_addCongrTable___closed__1;
x_80 = lean_ctor_get_uint8(x_77, sizeof(void*)*6 + 6);
lean_dec(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_free_object(x_75);
lean_free_object(x_64);
lean_dec(x_66);
lean_free_object(x_11);
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_apply_10(x_79, x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = l_Lean_indentExpr(x_1);
x_84 = l_Lean_Meta_Grind_addCongrTable___closed__3;
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_83);
lean_ctor_set(x_75, 0, x_84);
x_85 = l_Lean_Meta_Grind_addCongrTable___closed__5;
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_85);
lean_ctor_set(x_64, 0, x_75);
x_86 = l_Lean_indentExpr(x_66);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_86);
lean_ctor_set(x_11, 0, x_64);
x_87 = l_Lean_Meta_Grind_addCongrTable___closed__7;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_11);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Meta_Grind_reportIssue(x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_apply_10(x_79, x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_75, 0);
x_94 = lean_ctor_get(x_75, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_75);
x_95 = l_Lean_Meta_Grind_addCongrTable___closed__1;
x_96 = lean_ctor_get_uint8(x_93, sizeof(void*)*6 + 6);
lean_dec(x_93);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_free_object(x_64);
lean_dec(x_66);
lean_free_object(x_11);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_apply_10(x_95, x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = l_Lean_indentExpr(x_1);
x_100 = l_Lean_Meta_Grind_addCongrTable___closed__3;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Meta_Grind_addCongrTable___closed__5;
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_102);
lean_ctor_set(x_64, 0, x_101);
x_103 = l_Lean_indentExpr(x_66);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_103);
lean_ctor_set(x_11, 0, x_64);
x_104 = l_Lean_Meta_Grind_addCongrTable___closed__7;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_11);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Meta_Grind_reportIssue(x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_apply_10(x_95, x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_free_object(x_64);
lean_free_object(x_11);
x_110 = lean_ctor_get(x_71, 1);
lean_inc(x_110);
lean_dec(x_71);
x_111 = lean_box(0);
x_112 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_66, x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_110);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_free_object(x_64);
lean_dec(x_66);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_71);
if (x_113 == 0)
{
return x_71;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_71, 0);
x_115 = lean_ctor_get(x_71, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_71);
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
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_64);
lean_free_object(x_11);
x_117 = lean_box(0);
x_118 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_66, x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_64, 0);
lean_inc(x_119);
lean_dec(x_64);
x_120 = l_Lean_Expr_getAppFn(x_1);
x_121 = l_Lean_Expr_getAppFn(x_119);
x_122 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_123 = l_Lean_Meta_Grind_hasSameType(x_120, x_121, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = l_Lean_Meta_Grind_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Meta_Grind_addCongrTable___closed__1;
x_132 = lean_ctor_get_uint8(x_128, sizeof(void*)*6 + 6);
lean_dec(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_130);
lean_dec(x_119);
lean_free_object(x_11);
lean_dec(x_1);
x_133 = lean_box(0);
x_134 = lean_apply_10(x_131, x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_135 = l_Lean_indentExpr(x_1);
x_136 = l_Lean_Meta_Grind_addCongrTable___closed__3;
if (lean_is_scalar(x_130)) {
 x_137 = lean_alloc_ctor(7, 2, 0);
} else {
 x_137 = x_130;
 lean_ctor_set_tag(x_137, 7);
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Meta_Grind_addCongrTable___closed__5;
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_indentExpr(x_119);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_140);
lean_ctor_set(x_11, 0, x_139);
x_141 = l_Lean_Meta_Grind_addCongrTable___closed__7;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_11);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_Meta_Grind_reportIssue(x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_apply_10(x_131, x_144, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_145);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_free_object(x_11);
x_147 = lean_ctor_get(x_123, 1);
lean_inc(x_147);
lean_dec(x_123);
x_148 = lean_box(0);
x_149 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_119, x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_147);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_119);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_ctor_get(x_123, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_123, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_152 = x_123;
} else {
 lean_dec_ref(x_123);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_121);
lean_dec(x_120);
lean_free_object(x_11);
x_154 = lean_box(0);
x_155 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_119, x_154, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_11, 0);
x_157 = lean_ctor_get(x_11, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_11);
x_158 = lean_ctor_get(x_156, 4);
lean_inc(x_158);
lean_inc(x_1);
x_159 = l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(x_156, x_158, x_1);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = lean_st_ref_take(x_2, x_157);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 4);
lean_inc(x_167);
x_168 = lean_ctor_get(x_161, 5);
lean_inc(x_168);
x_169 = lean_ctor_get(x_161, 6);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_161, sizeof(void*)*15);
x_171 = lean_ctor_get(x_161, 7);
lean_inc(x_171);
x_172 = lean_ctor_get(x_161, 8);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 9);
lean_inc(x_173);
x_174 = lean_ctor_get(x_161, 10);
lean_inc(x_174);
x_175 = lean_ctor_get(x_161, 11);
lean_inc(x_175);
x_176 = lean_ctor_get(x_161, 12);
lean_inc(x_176);
x_177 = lean_ctor_get(x_161, 13);
lean_inc(x_177);
x_178 = lean_ctor_get(x_161, 14);
lean_inc(x_178);
x_179 = lean_box(0);
lean_inc(x_161);
x_180 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(x_161, x_167, x_1, x_179);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 lean_ctor_release(x_161, 6);
 lean_ctor_release(x_161, 7);
 lean_ctor_release(x_161, 8);
 lean_ctor_release(x_161, 9);
 lean_ctor_release(x_161, 10);
 lean_ctor_release(x_161, 11);
 lean_ctor_release(x_161, 12);
 lean_ctor_release(x_161, 13);
 lean_ctor_release(x_161, 14);
 x_181 = x_161;
} else {
 lean_dec_ref(x_161);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 15, 1);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_163);
lean_ctor_set(x_182, 1, x_164);
lean_ctor_set(x_182, 2, x_165);
lean_ctor_set(x_182, 3, x_166);
lean_ctor_set(x_182, 4, x_180);
lean_ctor_set(x_182, 5, x_168);
lean_ctor_set(x_182, 6, x_169);
lean_ctor_set(x_182, 7, x_171);
lean_ctor_set(x_182, 8, x_172);
lean_ctor_set(x_182, 9, x_173);
lean_ctor_set(x_182, 10, x_174);
lean_ctor_set(x_182, 11, x_175);
lean_ctor_set(x_182, 12, x_176);
lean_ctor_set(x_182, 13, x_177);
lean_ctor_set(x_182, 14, x_178);
lean_ctor_set_uint8(x_182, sizeof(void*)*15, x_170);
x_183 = lean_st_ref_set(x_2, x_182, x_162);
lean_dec(x_2);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_179);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_187 = lean_ctor_get(x_159, 0);
lean_inc(x_187);
lean_dec(x_159);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
x_190 = l_Lean_Expr_getAppFn(x_1);
x_191 = l_Lean_Expr_getAppFn(x_188);
x_192 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_190, x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_193 = l_Lean_Meta_Grind_hasSameType(x_190, x_191, x_6, x_7, x_8, x_9, x_157);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = l_Lean_Meta_Grind_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_196);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
x_201 = l_Lean_Meta_Grind_addCongrTable___closed__1;
x_202 = lean_ctor_get_uint8(x_198, sizeof(void*)*6 + 6);
lean_dec(x_198);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_200);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_1);
x_203 = lean_box(0);
x_204 = lean_apply_10(x_201, x_203, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_199);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_205 = l_Lean_indentExpr(x_1);
x_206 = l_Lean_Meta_Grind_addCongrTable___closed__3;
if (lean_is_scalar(x_200)) {
 x_207 = lean_alloc_ctor(7, 2, 0);
} else {
 x_207 = x_200;
 lean_ctor_set_tag(x_207, 7);
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Lean_Meta_Grind_addCongrTable___closed__5;
if (lean_is_scalar(x_189)) {
 x_209 = lean_alloc_ctor(7, 2, 0);
} else {
 x_209 = x_189;
 lean_ctor_set_tag(x_209, 7);
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_indentExpr(x_188);
x_211 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Lean_Meta_Grind_addCongrTable___closed__7;
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_Meta_Grind_reportIssue(x_213, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_199);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_apply_10(x_201, x_215, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_216);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_189);
x_218 = lean_ctor_get(x_193, 1);
lean_inc(x_218);
lean_dec(x_193);
x_219 = lean_box(0);
x_220 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_188, x_219, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_218);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = lean_ctor_get(x_193, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_193, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_223 = x_193;
} else {
 lean_dec_ref(x_193);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
x_225 = lean_box(0);
x_226 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_188, x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_226;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_addCongrTable___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_5, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
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
x_14 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_12);
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
x_22 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
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
x_29 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_27);
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
x_39 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_HeadIndex_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_HeadIndex_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_17);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
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
x_21 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_4, x_19);
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
x_28 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_4, x_26);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
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
x_63 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_4, x_60);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(x_1, x_83, x_4, x_5);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(x_96, x_97, x_4, x_5);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_HeadIndex_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Expr_toHeadIndex(x_1);
x_12 = lean_st_ref_take(x_2, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_17, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_1);
x_20 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_17, x_11, x_12);
lean_ctor_set(x_14, 5, x_20);
x_21 = lean_st_ref_set(x_2, x_14, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_28);
lean_ctor_set(x_12, 0, x_1);
x_29 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_17, x_11, x_12);
lean_ctor_set(x_14, 5, x_29);
x_30 = lean_st_ref_set(x_2, x_14, x_16);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_37 = lean_ctor_get(x_12, 1);
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
x_40 = lean_ctor_get(x_14, 2);
x_41 = lean_ctor_get(x_14, 3);
x_42 = lean_ctor_get(x_14, 4);
x_43 = lean_ctor_get(x_14, 5);
x_44 = lean_ctor_get(x_14, 6);
x_45 = lean_ctor_get_uint8(x_14, sizeof(void*)*15);
x_46 = lean_ctor_get(x_14, 7);
x_47 = lean_ctor_get(x_14, 8);
x_48 = lean_ctor_get(x_14, 9);
x_49 = lean_ctor_get(x_14, 10);
x_50 = lean_ctor_get(x_14, 11);
x_51 = lean_ctor_get(x_14, 12);
x_52 = lean_ctor_get(x_14, 13);
x_53 = lean_ctor_get(x_14, 14);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
lean_inc(x_43);
x_54 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_43, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_55);
lean_ctor_set(x_12, 0, x_1);
x_56 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_43, x_11, x_12);
x_57 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_57, 0, x_38);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_40);
lean_ctor_set(x_57, 3, x_41);
lean_ctor_set(x_57, 4, x_42);
lean_ctor_set(x_57, 5, x_56);
lean_ctor_set(x_57, 6, x_44);
lean_ctor_set(x_57, 7, x_46);
lean_ctor_set(x_57, 8, x_47);
lean_ctor_set(x_57, 9, x_48);
lean_ctor_set(x_57, 10, x_49);
lean_ctor_set(x_57, 11, x_50);
lean_ctor_set(x_57, 12, x_51);
lean_ctor_set(x_57, 13, x_52);
lean_ctor_set(x_57, 14, x_53);
lean_ctor_set_uint8(x_57, sizeof(void*)*15, x_45);
x_58 = lean_st_ref_set(x_2, x_57, x_37);
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
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
lean_dec(x_54);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_63);
lean_ctor_set(x_12, 0, x_1);
x_64 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_43, x_11, x_12);
x_65 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_65, 0, x_38);
lean_ctor_set(x_65, 1, x_39);
lean_ctor_set(x_65, 2, x_40);
lean_ctor_set(x_65, 3, x_41);
lean_ctor_set(x_65, 4, x_42);
lean_ctor_set(x_65, 5, x_64);
lean_ctor_set(x_65, 6, x_44);
lean_ctor_set(x_65, 7, x_46);
lean_ctor_set(x_65, 8, x_47);
lean_ctor_set(x_65, 9, x_48);
lean_ctor_set(x_65, 10, x_49);
lean_ctor_set(x_65, 11, x_50);
lean_ctor_set(x_65, 12, x_51);
lean_ctor_set(x_65, 13, x_52);
lean_ctor_set(x_65, 14, x_53);
lean_ctor_set_uint8(x_65, sizeof(void*)*15, x_45);
x_66 = lean_st_ref_set(x_2, x_65, x_37);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_71 = lean_ctor_get(x_12, 0);
x_72 = lean_ctor_get(x_12, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_12);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 6);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_71, sizeof(void*)*15);
x_81 = lean_ctor_get(x_71, 7);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 8);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 9);
lean_inc(x_83);
x_84 = lean_ctor_get(x_71, 10);
lean_inc(x_84);
x_85 = lean_ctor_get(x_71, 11);
lean_inc(x_85);
x_86 = lean_ctor_get(x_71, 12);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 13);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 14);
lean_inc(x_88);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 lean_ctor_release(x_71, 6);
 lean_ctor_release(x_71, 7);
 lean_ctor_release(x_71, 8);
 lean_ctor_release(x_71, 9);
 lean_ctor_release(x_71, 10);
 lean_ctor_release(x_71, 11);
 lean_ctor_release(x_71, 12);
 lean_ctor_release(x_71, 13);
 lean_ctor_release(x_71, 14);
 x_89 = x_71;
} else {
 lean_dec_ref(x_71);
 x_89 = lean_box(0);
}
lean_inc(x_78);
x_90 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_78, x_11);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_78, x_11, x_92);
if (lean_is_scalar(x_89)) {
 x_94 = lean_alloc_ctor(0, 15, 1);
} else {
 x_94 = x_89;
}
lean_ctor_set(x_94, 0, x_73);
lean_ctor_set(x_94, 1, x_74);
lean_ctor_set(x_94, 2, x_75);
lean_ctor_set(x_94, 3, x_76);
lean_ctor_set(x_94, 4, x_77);
lean_ctor_set(x_94, 5, x_93);
lean_ctor_set(x_94, 6, x_79);
lean_ctor_set(x_94, 7, x_81);
lean_ctor_set(x_94, 8, x_82);
lean_ctor_set(x_94, 9, x_83);
lean_ctor_set(x_94, 10, x_84);
lean_ctor_set(x_94, 11, x_85);
lean_ctor_set(x_94, 12, x_86);
lean_ctor_set(x_94, 13, x_87);
lean_ctor_set(x_94, 14, x_88);
lean_ctor_set_uint8(x_94, sizeof(void*)*15, x_80);
x_95 = lean_st_ref_set(x_2, x_94, x_72);
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
x_98 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
lean_dec(x_90);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_78, x_11, x_101);
if (lean_is_scalar(x_89)) {
 x_103 = lean_alloc_ctor(0, 15, 1);
} else {
 x_103 = x_89;
}
lean_ctor_set(x_103, 0, x_73);
lean_ctor_set(x_103, 1, x_74);
lean_ctor_set(x_103, 2, x_75);
lean_ctor_set(x_103, 3, x_76);
lean_ctor_set(x_103, 4, x_77);
lean_ctor_set(x_103, 5, x_102);
lean_ctor_set(x_103, 6, x_79);
lean_ctor_set(x_103, 7, x_81);
lean_ctor_set(x_103, 8, x_82);
lean_ctor_set(x_103, 9, x_83);
lean_ctor_set(x_103, 10, x_84);
lean_ctor_set(x_103, 11, x_85);
lean_ctor_set(x_103, 12, x_86);
lean_ctor_set(x_103, 13, x_87);
lean_ctor_set(x_103, 14, x_88);
lean_ctor_set_uint8(x_103, sizeof(void*)*15, x_80);
x_104 = lean_st_ref_set(x_2, x_103, x_72);
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
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 12);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 12);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
x_22 = lean_st_ref_set(x_3, x_13, x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 2);
x_31 = lean_ctor_get(x_14, 3);
x_32 = lean_ctor_get(x_14, 4);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_33);
lean_inc(x_29);
lean_dec(x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_33);
lean_ctor_set(x_12, 0, x_1);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_32);
lean_ctor_set(x_13, 12, x_34);
x_35 = lean_st_ref_set(x_3, x_13, x_16);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
x_42 = lean_ctor_get(x_13, 2);
x_43 = lean_ctor_get(x_13, 3);
x_44 = lean_ctor_get(x_13, 4);
x_45 = lean_ctor_get(x_13, 5);
x_46 = lean_ctor_get(x_13, 6);
x_47 = lean_ctor_get_uint8(x_13, sizeof(void*)*15);
x_48 = lean_ctor_get(x_13, 7);
x_49 = lean_ctor_get(x_13, 8);
x_50 = lean_ctor_get(x_13, 9);
x_51 = lean_ctor_get(x_13, 10);
x_52 = lean_ctor_get(x_13, 11);
x_53 = lean_ctor_get(x_13, 13);
x_54 = lean_ctor_get(x_13, 14);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
x_55 = lean_ctor_get(x_14, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_14, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_14, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_14, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_60 = x_14;
} else {
 lean_dec_ref(x_14);
 x_60 = lean_box(0);
}
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_59);
lean_ctor_set(x_12, 0, x_1);
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 5, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_12);
lean_ctor_set(x_61, 2, x_56);
lean_ctor_set(x_61, 3, x_57);
lean_ctor_set(x_61, 4, x_58);
x_62 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_62, 0, x_40);
lean_ctor_set(x_62, 1, x_41);
lean_ctor_set(x_62, 2, x_42);
lean_ctor_set(x_62, 3, x_43);
lean_ctor_set(x_62, 4, x_44);
lean_ctor_set(x_62, 5, x_45);
lean_ctor_set(x_62, 6, x_46);
lean_ctor_set(x_62, 7, x_48);
lean_ctor_set(x_62, 8, x_49);
lean_ctor_set(x_62, 9, x_50);
lean_ctor_set(x_62, 10, x_51);
lean_ctor_set(x_62, 11, x_52);
lean_ctor_set(x_62, 12, x_61);
lean_ctor_set(x_62, 13, x_53);
lean_ctor_set(x_62, 14, x_54);
lean_ctor_set_uint8(x_62, sizeof(void*)*15, x_47);
x_63 = lean_st_ref_set(x_3, x_62, x_16);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_68 = lean_ctor_get(x_12, 1);
lean_inc(x_68);
lean_dec(x_12);
x_69 = lean_ctor_get(x_13, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_13, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_13, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_13, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_13, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_13, 6);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_13, sizeof(void*)*15);
x_77 = lean_ctor_get(x_13, 7);
lean_inc(x_77);
x_78 = lean_ctor_get(x_13, 8);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 9);
lean_inc(x_79);
x_80 = lean_ctor_get(x_13, 10);
lean_inc(x_80);
x_81 = lean_ctor_get(x_13, 11);
lean_inc(x_81);
x_82 = lean_ctor_get(x_13, 13);
lean_inc(x_82);
x_83 = lean_ctor_get(x_13, 14);
lean_inc(x_83);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 lean_ctor_release(x_13, 9);
 lean_ctor_release(x_13, 10);
 lean_ctor_release(x_13, 11);
 lean_ctor_release(x_13, 12);
 lean_ctor_release(x_13, 13);
 lean_ctor_release(x_13, 14);
 x_84 = x_13;
} else {
 lean_dec_ref(x_13);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_14, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_14, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_14, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_14, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_14, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_90 = x_14;
} else {
 lean_dec_ref(x_14);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_89);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 5, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_86);
lean_ctor_set(x_92, 3, x_87);
lean_ctor_set(x_92, 4, x_88);
if (lean_is_scalar(x_84)) {
 x_93 = lean_alloc_ctor(0, 15, 1);
} else {
 x_93 = x_84;
}
lean_ctor_set(x_93, 0, x_69);
lean_ctor_set(x_93, 1, x_70);
lean_ctor_set(x_93, 2, x_71);
lean_ctor_set(x_93, 3, x_72);
lean_ctor_set(x_93, 4, x_73);
lean_ctor_set(x_93, 5, x_74);
lean_ctor_set(x_93, 6, x_75);
lean_ctor_set(x_93, 7, x_77);
lean_ctor_set(x_93, 8, x_78);
lean_ctor_set(x_93, 9, x_79);
lean_ctor_set(x_93, 10, x_80);
lean_ctor_set(x_93, 11, x_81);
lean_ctor_set(x_93, 12, x_92);
lean_ctor_set(x_93, 13, x_82);
lean_ctor_set(x_93, 14, x_83);
lean_ctor_set_uint8(x_93, sizeof(void*)*15, x_76);
x_94 = lean_st_ref_set(x_3, x_93, x_68);
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
x_97 = lean_box(0);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("candidate", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3;
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
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_1);
x_23 = l_Lean_MessageData_ofExpr(x_1);
x_24 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_27);
return x_29;
}
else
{
uint8_t x_30; 
lean_free_object(x_12);
lean_dec(x_1);
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
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_1);
x_37 = l_Lean_MessageData_ofExpr(x_1);
x_38 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup(x_2, lean_box(0));
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_appFnCleanup(x_5, lean_box(0));
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Expr_appArg(x_8, lean_box(0));
x_12 = l_Lean_Expr_appFnCleanup(x_8, lean_box(0));
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2;
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Expr_isProp(x_11);
lean_dec(x_11);
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMorallyIff___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isMorallyIff(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_isMatcherAppCore(x_14, x_1);
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
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_isMatcherAppCore(x_19, x_1);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 12);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Meta_Grind_getConfig___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*6 + 4);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_isInductivePredicate(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes;
x_15 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(x_13, x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_getConfig___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*6 + 2);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_26 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
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
lean_dec(x_27);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
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
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
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
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
return x_26;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_26);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_inc(x_1);
x_12 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
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
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
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
x_14 = l_Lean_Meta_whnfD(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Expr_getAppFn(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_2, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 12);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_25, x_19);
lean_dec(x_19);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; 
lean_free_object(x_20);
x_28 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 12);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_32, x_19);
lean_dec(x_19);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_14, 0, x_37);
return x_14;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = l_Lean_Expr_getAppFn(x_38);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_get(x_2, x_39);
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
x_46 = lean_ctor_get(x_43, 12);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_47, x_41);
lean_dec(x_41);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_45);
x_51 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_39);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_11);
if (x_58 == 0)
{
return x_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
case 5:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Meta_Grind_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*6 + 3);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_box(0);
x_67 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(x_1, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
return x_67;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = l_Lean_Expr_isIte(x_1);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isDIte(x_1);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
x_72 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(x_1, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
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
lean_object* x_84; 
x_84 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_84);
if (x_91 == 0)
{
return x_84;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_84, 0);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_84);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
default: 
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_10);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqRecOn_heq", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = l_Lean_Expr_constLevels_x21(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
lean_inc(x_8);
x_21 = l_Lean_mkApp6(x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = 1;
x_23 = l_Lean_Meta_Grind_pushEqCore(x_1, x_8, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqNDRec_heq", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = l_Lean_Expr_constLevels_x21(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
lean_inc(x_6);
x_21 = l_Lean_mkApp6(x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = 1;
x_23 = l_Lean_Meta_Grind_pushEqCore(x_1, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqRec_heq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = l_Lean_Expr_constLevels_x21(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
lean_inc(x_6);
x_21 = l_Lean_mkApp6(x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = 1;
x_23 = l_Lean_Meta_Grind_pushEqCore(x_1, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast_heq", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = l_Lean_Expr_constLevels_x21(x_2);
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2;
x_18 = l_Lean_Expr_const___override(x_17, x_16);
lean_inc(x_6);
x_19 = l_Lean_mkApp4(x_18, x_3, x_4, x_5, x_6);
x_20 = 1;
x_21 = l_Lean_Meta_Grind_pushEqCore(x_1, x_6, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recOn", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_13);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Expr_appArg(x_15, lean_box(0));
x_19 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Expr_appArg(x_19, lean_box(0));
x_23 = l_Lean_Expr_appFnCleanup(x_19, lean_box(0));
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Expr_appArg(x_23, lean_box(0));
x_27 = l_Lean_Expr_appFnCleanup(x_23, lean_box(0));
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Lean_Expr_appArg(x_27, lean_box(0));
x_31 = l_Lean_Expr_appFnCleanup(x_27, lean_box(0));
x_32 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2;
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Expr_isApp(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_11, 0, x_35);
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_Expr_appArg(x_31, lean_box(0));
x_37 = l_Lean_Expr_appFnCleanup(x_31, lean_box(0));
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_1);
x_39 = lean_box(0);
lean_ctor_set(x_11, 0, x_39);
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = l_Lean_Expr_appArg(x_37, lean_box(0));
x_41 = l_Lean_Expr_appFnCleanup(x_37, lean_box(0));
x_42 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4;
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6;
x_45 = l_Lean_Expr_isConstOf(x_41, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8;
x_47 = l_Lean_Expr_isConstOf(x_41, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_11, 0, x_48);
return x_11;
}
else
{
lean_object* x_49; 
lean_free_object(x_11);
x_49 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(x_1, x_41, x_40, x_36, x_30, x_26, x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_41);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_free_object(x_11);
x_50 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(x_1, x_41, x_40, x_36, x_30, x_26, x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_41);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_free_object(x_11);
x_51 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(x_1, x_41, x_40, x_36, x_30, x_26, x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_41);
return x_51;
}
}
}
}
else
{
lean_object* x_52; 
lean_free_object(x_11);
x_52 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(x_1, x_31, x_30, x_26, x_22, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_31);
return x_52;
}
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = l_Lean_Expr_cleanupAnnotations(x_53);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Expr_appArg(x_55, lean_box(0));
x_60 = l_Lean_Expr_appFnCleanup(x_55, lean_box(0));
x_61 = l_Lean_Expr_isApp(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = l_Lean_Expr_appArg(x_60, lean_box(0));
x_65 = l_Lean_Expr_appFnCleanup(x_60, lean_box(0));
x_66 = l_Lean_Expr_isApp(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_54);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = l_Lean_Expr_appArg(x_65, lean_box(0));
x_70 = l_Lean_Expr_appFnCleanup(x_65, lean_box(0));
x_71 = l_Lean_Expr_isApp(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_54);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = l_Lean_Expr_appArg(x_70, lean_box(0));
x_75 = l_Lean_Expr_appFnCleanup(x_70, lean_box(0));
x_76 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2;
x_77 = l_Lean_Expr_isConstOf(x_75, x_76);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_isApp(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_54);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = l_Lean_Expr_appArg(x_75, lean_box(0));
x_82 = l_Lean_Expr_appFnCleanup(x_75, lean_box(0));
x_83 = l_Lean_Expr_isApp(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_54);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = l_Lean_Expr_appArg(x_82, lean_box(0));
x_87 = l_Lean_Expr_appFnCleanup(x_82, lean_box(0));
x_88 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4;
x_89 = l_Lean_Expr_isConstOf(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6;
x_91 = l_Lean_Expr_isConstOf(x_87, x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8;
x_93 = l_Lean_Expr_isConstOf(x_87, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_81);
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_1);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_54);
return x_95;
}
else
{
lean_object* x_96; 
x_96 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(x_1, x_87, x_86, x_81, x_74, x_69, x_64, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_87);
return x_96;
}
}
else
{
lean_object* x_97; 
x_97 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(x_1, x_87, x_86, x_81, x_74, x_69, x_64, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_87);
return x_97;
}
}
else
{
lean_object* x_98; 
x_98 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(x_1, x_87, x_86, x_81, x_74, x_69, x_64, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_87);
return x_98;
}
}
}
}
else
{
lean_object* x_99; 
x_99 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(x_1, x_75, x_74, x_69, x_64, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_75);
return x_99;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1;
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Core_transform___at_Lean_Meta_Grind_unfoldReducible___spec__1(x_1, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3;
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4;
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_14, x_16, x_17, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__5;
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_19, x_21, x_17, x_8, x_9, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Meta_Grind_canon(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Grind_shareCommon(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_12, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(x_16, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_18, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_array_set(x_3, x_4, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_2 = x_14;
x_3 = x_16;
x_4 = x_18;
goto _start;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_dec(x_4);
x_20 = lean_array_size(x_3);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(x_1, x_20, x_21, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_mkAppN(x_2, x_24);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = l_Lean_mkAppN(x_2, x_26);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isBVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_14 = lean_expr_eqv(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_groundPattern_x3f(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__2(x_2, x_1, x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
lean_inc(x_25);
x_28 = lean_grind_internalize(x_25, x_2, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l_Lean_Meta_Grind_mkGroundPattern(x_25);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lean_Meta_Grind_mkGroundPattern(x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_25);
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
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_11);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_4, x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_4);
x_18 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_17);
x_19 = lean_grind_internalize(x_17, x_2, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_registerParent(x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_6 = x_22;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_15);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_mkEqRefl(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l_Lean_Meta_Grind_pushEqCore(x_1, x_2, x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("auxiliary application", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1(x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_3);
x_25 = l_Lean_indentExpr(x_3);
x_26 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__2;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_25);
lean_ctor_set(x_14, 0, x_26);
x_27 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_1, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1(x_2, x_3, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
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
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_3);
x_40 = l_Lean_indentExpr(x_3);
x_41 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_1, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1(x_2, x_3, x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
lean_dec(x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_51 = x_38;
} else {
 lean_dec_ref(x_38);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchCond", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lambda", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__1;
x_4 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(idx := ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_12 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_12, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_17 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_29 = lean_grind_internalize(x_22, x_2, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_32 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_18);
lean_free_object(x_13);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_31, x_1, x_22, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 1);
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_41 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Expr_getAppFn(x_22);
x_44 = lean_st_ref_get(x_3, x_42);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_43);
x_48 = l_Lean_Meta_Grind_Goal_getENode(x_46, x_43, x_9, x_10, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 7);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Init_Data_Repr_0__Nat_reprFast(x_51);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_54);
lean_ctor_set(x_44, 0, x_55);
x_56 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_56);
lean_ctor_set(x_32, 0, x_44);
x_57 = l_Lean_MessageData_ofExpr(x_43);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_57);
lean_ctor_set(x_18, 0, x_32);
x_58 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_58);
lean_ctor_set(x_13, 0, x_18);
x_59 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_31, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_31, x_1, x_22, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_60);
return x_62;
}
else
{
uint8_t x_63; 
lean_free_object(x_44);
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_48);
if (x_63 == 0)
{
return x_48;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_48, 0);
x_65 = lean_ctor_get(x_48, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_48);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_44, 0);
x_68 = lean_ctor_get(x_44, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_44);
lean_inc(x_43);
x_69 = l_Lean_Meta_Grind_Goal_getENode(x_67, x_43, x_9, x_10, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 7);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l___private_Init_Data_Repr_0__Nat_reprFast(x_72);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_MessageData_ofFormat(x_74);
x_76 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_78);
lean_ctor_set(x_32, 0, x_77);
x_79 = l_Lean_MessageData_ofExpr(x_43);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_79);
lean_ctor_set(x_18, 0, x_32);
x_80 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_80);
lean_ctor_set(x_13, 0, x_18);
x_81 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_31, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_31, x_1, x_22, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_83);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_43);
lean_free_object(x_32);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_85 = lean_ctor_get(x_69, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_69, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_87 = x_69;
} else {
 lean_dec_ref(x_69);
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
}
else
{
uint8_t x_89; 
lean_free_object(x_32);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_41);
if (x_89 == 0)
{
return x_41;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_41, 0);
x_91 = lean_ctor_get(x_41, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
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
x_93 = lean_ctor_get(x_32, 1);
lean_inc(x_93);
lean_dec(x_32);
x_94 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Expr_getAppFn(x_22);
x_97 = lean_st_ref_get(x_3, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
lean_inc(x_96);
x_101 = l_Lean_Meta_Grind_Goal_getENode(x_98, x_96, x_9, x_10, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 7);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l___private_Init_Data_Repr_0__Nat_reprFast(x_104);
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_MessageData_ofFormat(x_106);
x_108 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_100;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_MessageData_ofExpr(x_96);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_112);
lean_ctor_set(x_18, 0, x_111);
x_113 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_113);
lean_ctor_set(x_13, 0, x_18);
x_114 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_31, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_31, x_1, x_22, x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_116);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_100);
lean_dec(x_96);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = lean_ctor_get(x_101, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_101, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_120 = x_101;
} else {
 lean_dec_ref(x_101);
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
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = lean_ctor_get(x_94, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_94, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_124 = x_94;
} else {
 lean_dec_ref(x_94);
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
}
}
else
{
uint8_t x_126; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_29);
if (x_126 == 0)
{
return x_29;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_29, 0);
x_128 = lean_ctor_get(x_29, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_29);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
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
x_130 = !lean_is_exclusive(x_26);
if (x_130 == 0)
{
return x_26;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_26, 0);
x_132 = lean_ctor_get(x_26, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_26);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_le(x_23, x_23);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_23);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_135 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_138 = lean_grind_internalize(x_22, x_2, x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_141 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_140, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_free_object(x_18);
lean_free_object(x_13);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_box(0);
x_146 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_140, x_1, x_22, x_145, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_146;
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_141);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_141, 1);
x_149 = lean_ctor_get(x_141, 0);
lean_dec(x_149);
x_150 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_Lean_Expr_getAppFn(x_22);
x_153 = lean_st_ref_get(x_3, x_151);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_152);
x_157 = l_Lean_Meta_Grind_Goal_getENode(x_155, x_152, x_9, x_10, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 7);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l___private_Init_Data_Repr_0__Nat_reprFast(x_160);
x_162 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = l_Lean_MessageData_ofFormat(x_162);
x_164 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
lean_ctor_set_tag(x_153, 7);
lean_ctor_set(x_153, 1, x_163);
lean_ctor_set(x_153, 0, x_164);
x_165 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_165);
lean_ctor_set(x_141, 0, x_153);
x_166 = l_Lean_MessageData_ofExpr(x_152);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_166);
lean_ctor_set(x_18, 0, x_141);
x_167 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_167);
lean_ctor_set(x_13, 0, x_18);
x_168 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_140, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_159);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_140, x_1, x_22, x_169, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_170);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_169);
return x_171;
}
else
{
uint8_t x_172; 
lean_free_object(x_153);
lean_dec(x_152);
lean_free_object(x_141);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_157);
if (x_172 == 0)
{
return x_157;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_157, 0);
x_174 = lean_ctor_get(x_157, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_157);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_153, 0);
x_177 = lean_ctor_get(x_153, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_153);
lean_inc(x_152);
x_178 = l_Lean_Meta_Grind_Goal_getENode(x_176, x_152, x_9, x_10, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 7);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l___private_Init_Data_Repr_0__Nat_reprFast(x_181);
x_183 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = l_Lean_MessageData_ofFormat(x_183);
x_185 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_187);
lean_ctor_set(x_141, 0, x_186);
x_188 = l_Lean_MessageData_ofExpr(x_152);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_188);
lean_ctor_set(x_18, 0, x_141);
x_189 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_189);
lean_ctor_set(x_13, 0, x_18);
x_190 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_140, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_180);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_140, x_1, x_22, x_191, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_192);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_191);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_152);
lean_free_object(x_141);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_194 = lean_ctor_get(x_178, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_178, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_196 = x_178;
} else {
 lean_dec_ref(x_178);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_free_object(x_141);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_150);
if (x_198 == 0)
{
return x_150;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_150, 0);
x_200 = lean_ctor_get(x_150, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_150);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_141, 1);
lean_inc(x_202);
lean_dec(x_141);
x_203 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Lean_Expr_getAppFn(x_22);
x_206 = lean_st_ref_get(x_3, x_204);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
lean_inc(x_205);
x_210 = l_Lean_Meta_Grind_Goal_getENode(x_207, x_205, x_9, x_10, x_208);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_ctor_get(x_211, 7);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l___private_Init_Data_Repr_0__Nat_reprFast(x_213);
x_215 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = l_Lean_MessageData_ofFormat(x_215);
x_217 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_209)) {
 x_218 = lean_alloc_ctor(7, 2, 0);
} else {
 x_218 = x_209;
 lean_ctor_set_tag(x_218, 7);
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_MessageData_ofExpr(x_205);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_221);
lean_ctor_set(x_18, 0, x_220);
x_222 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_222);
lean_ctor_set(x_13, 0, x_18);
x_223 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_140, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_212);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_140, x_1, x_22, x_224, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_225);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_224);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_209);
lean_dec(x_205);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_227 = lean_ctor_get(x_210, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_210, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_229 = x_210;
} else {
 lean_dec_ref(x_210);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_231 = lean_ctor_get(x_203, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_203, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_233 = x_203;
} else {
 lean_dec_ref(x_203);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
}
else
{
uint8_t x_235; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_138);
if (x_235 == 0)
{
return x_138;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_138, 0);
x_237 = lean_ctor_get(x_138, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_138);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
uint8_t x_239; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
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
x_239 = !lean_is_exclusive(x_135);
if (x_239 == 0)
{
return x_135;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_135, 0);
x_241 = lean_ctor_get(x_135, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_135);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
size_t x_243; size_t x_244; lean_object* x_245; lean_object* x_246; 
x_243 = 0;
x_244 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_245 = lean_box(0);
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
x_246 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(x_1, x_2, x_21, x_243, x_244, x_245, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_21);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_248 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
x_251 = lean_grind_internalize(x_22, x_2, x_250, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_253 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_254 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_253, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_252);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
lean_free_object(x_18);
lean_free_object(x_13);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_253, x_1, x_22, x_245, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_257);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_258;
}
else
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_254);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_254, 1);
x_261 = lean_ctor_get(x_254, 0);
lean_dec(x_261);
x_262 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_260);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = l_Lean_Expr_getAppFn(x_22);
x_265 = lean_st_ref_get(x_3, x_263);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_265, 0);
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_264);
x_269 = l_Lean_Meta_Grind_Goal_getENode(x_267, x_264, x_9, x_10, x_268);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 7);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l___private_Init_Data_Repr_0__Nat_reprFast(x_272);
x_274 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = l_Lean_MessageData_ofFormat(x_274);
x_276 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
lean_ctor_set_tag(x_265, 7);
lean_ctor_set(x_265, 1, x_275);
lean_ctor_set(x_265, 0, x_276);
x_277 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
lean_ctor_set_tag(x_254, 7);
lean_ctor_set(x_254, 1, x_277);
lean_ctor_set(x_254, 0, x_265);
x_278 = l_Lean_MessageData_ofExpr(x_264);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_278);
lean_ctor_set(x_18, 0, x_254);
x_279 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_279);
lean_ctor_set(x_13, 0, x_18);
x_280 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_253, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_271);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_253, x_1, x_22, x_281, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_282);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_281);
return x_283;
}
else
{
uint8_t x_284; 
lean_free_object(x_265);
lean_dec(x_264);
lean_free_object(x_254);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_269);
if (x_284 == 0)
{
return x_269;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_269, 0);
x_286 = lean_ctor_get(x_269, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_269);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_265, 0);
x_289 = lean_ctor_get(x_265, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_265);
lean_inc(x_264);
x_290 = l_Lean_Meta_Grind_Goal_getENode(x_288, x_264, x_9, x_10, x_289);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 7);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l___private_Init_Data_Repr_0__Nat_reprFast(x_293);
x_295 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_295, 0, x_294);
x_296 = l_Lean_MessageData_ofFormat(x_295);
x_297 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
x_298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
x_299 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
lean_ctor_set_tag(x_254, 7);
lean_ctor_set(x_254, 1, x_299);
lean_ctor_set(x_254, 0, x_298);
x_300 = l_Lean_MessageData_ofExpr(x_264);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_300);
lean_ctor_set(x_18, 0, x_254);
x_301 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_301);
lean_ctor_set(x_13, 0, x_18);
x_302 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_253, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_292);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_253, x_1, x_22, x_303, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_304);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_303);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_264);
lean_free_object(x_254);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_306 = lean_ctor_get(x_290, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_290, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_308 = x_290;
} else {
 lean_dec_ref(x_290);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_free_object(x_254);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_262);
if (x_310 == 0)
{
return x_262;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_262, 0);
x_312 = lean_ctor_get(x_262, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_262);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_254, 1);
lean_inc(x_314);
lean_dec(x_254);
x_315 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = l_Lean_Expr_getAppFn(x_22);
x_318 = lean_st_ref_get(x_3, x_316);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_321 = x_318;
} else {
 lean_dec_ref(x_318);
 x_321 = lean_box(0);
}
lean_inc(x_317);
x_322 = l_Lean_Meta_Grind_Goal_getENode(x_319, x_317, x_9, x_10, x_320);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_323, 7);
lean_inc(x_325);
lean_dec(x_323);
x_326 = l___private_Init_Data_Repr_0__Nat_reprFast(x_325);
x_327 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_327, 0, x_326);
x_328 = l_Lean_MessageData_ofFormat(x_327);
x_329 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_321)) {
 x_330 = lean_alloc_ctor(7, 2, 0);
} else {
 x_330 = x_321;
 lean_ctor_set_tag(x_330, 7);
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
x_332 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Lean_MessageData_ofExpr(x_317);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_333);
lean_ctor_set(x_18, 0, x_332);
x_334 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_334);
lean_ctor_set(x_13, 0, x_18);
x_335 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_253, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_324);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_253, x_1, x_22, x_336, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_337);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_336);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_321);
lean_dec(x_317);
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_339 = lean_ctor_get(x_322, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_322, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_341 = x_322;
} else {
 lean_dec_ref(x_322);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_343 = lean_ctor_get(x_315, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_315, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_345 = x_315;
} else {
 lean_dec_ref(x_315);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
}
}
else
{
uint8_t x_347; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_347 = !lean_is_exclusive(x_251);
if (x_347 == 0)
{
return x_251;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_251, 0);
x_349 = lean_ctor_get(x_251, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_251);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
uint8_t x_351; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
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
x_351 = !lean_is_exclusive(x_248);
if (x_351 == 0)
{
return x_248;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_248, 0);
x_353 = lean_ctor_get(x_248, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_248);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
uint8_t x_355; 
lean_free_object(x_18);
lean_dec(x_22);
lean_free_object(x_13);
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
x_355 = !lean_is_exclusive(x_246);
if (x_355 == 0)
{
return x_246;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_246, 0);
x_357 = lean_ctor_get(x_246, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_246);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_359 = lean_ctor_get(x_18, 0);
x_360 = lean_ctor_get(x_18, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_18);
x_361 = lean_array_get_size(x_359);
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_nat_dec_lt(x_362, x_361);
if (x_363 == 0)
{
lean_object* x_364; 
lean_dec(x_361);
lean_dec(x_359);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_364 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_360);
x_367 = lean_grind_internalize(x_360, x_2, x_366, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_365);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_369 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_370 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_369, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_368);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_unbox(x_371);
lean_dec(x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_free_object(x_13);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
lean_dec(x_370);
x_374 = lean_box(0);
x_375 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_369, x_1, x_360, x_374, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_373);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_370, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_377 = x_370;
} else {
 lean_dec_ref(x_370);
 x_377 = lean_box(0);
}
x_378 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_376);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
x_380 = l_Lean_Expr_getAppFn(x_360);
x_381 = lean_st_ref_get(x_3, x_379);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_384 = x_381;
} else {
 lean_dec_ref(x_381);
 x_384 = lean_box(0);
}
lean_inc(x_380);
x_385 = l_Lean_Meta_Grind_Goal_getENode(x_382, x_380, x_9, x_10, x_383);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_ctor_get(x_386, 7);
lean_inc(x_388);
lean_dec(x_386);
x_389 = l___private_Init_Data_Repr_0__Nat_reprFast(x_388);
x_390 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_390, 0, x_389);
x_391 = l_Lean_MessageData_ofFormat(x_390);
x_392 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_384)) {
 x_393 = lean_alloc_ctor(7, 2, 0);
} else {
 x_393 = x_384;
 lean_ctor_set_tag(x_393, 7);
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_391);
x_394 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
if (lean_is_scalar(x_377)) {
 x_395 = lean_alloc_ctor(7, 2, 0);
} else {
 x_395 = x_377;
 lean_ctor_set_tag(x_395, 7);
}
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = l_Lean_MessageData_ofExpr(x_380);
x_397 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
x_398 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_398);
lean_ctor_set(x_13, 0, x_397);
x_399 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_369, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_387);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_402 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_369, x_1, x_360, x_400, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_401);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_400);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_384);
lean_dec(x_380);
lean_dec(x_377);
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_403 = lean_ctor_get(x_385, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_385, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_405 = x_385;
} else {
 lean_dec_ref(x_385);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_377);
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_407 = lean_ctor_get(x_378, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_378, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_409 = x_378;
} else {
 lean_dec_ref(x_378);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_411 = lean_ctor_get(x_367, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_367, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_413 = x_367;
} else {
 lean_dec_ref(x_367);
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
lean_dec(x_360);
lean_free_object(x_13);
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
x_415 = lean_ctor_get(x_364, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_364, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_417 = x_364;
} else {
 lean_dec_ref(x_364);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
else
{
uint8_t x_419; 
x_419 = lean_nat_dec_le(x_361, x_361);
if (x_419 == 0)
{
lean_object* x_420; 
lean_dec(x_361);
lean_dec(x_359);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_420 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_422 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_360);
x_423 = lean_grind_internalize(x_360, x_2, x_422, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_421);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_426 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_425, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_424);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_unbox(x_427);
lean_dec(x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_free_object(x_13);
x_429 = lean_ctor_get(x_426, 1);
lean_inc(x_429);
lean_dec(x_426);
x_430 = lean_box(0);
x_431 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_425, x_1, x_360, x_430, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_429);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_426, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_433 = x_426;
} else {
 lean_dec_ref(x_426);
 x_433 = lean_box(0);
}
x_434 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_432);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
x_436 = l_Lean_Expr_getAppFn(x_360);
x_437 = lean_st_ref_get(x_3, x_435);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
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
lean_inc(x_436);
x_441 = l_Lean_Meta_Grind_Goal_getENode(x_438, x_436, x_9, x_10, x_439);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
lean_dec(x_441);
x_444 = lean_ctor_get(x_442, 7);
lean_inc(x_444);
lean_dec(x_442);
x_445 = l___private_Init_Data_Repr_0__Nat_reprFast(x_444);
x_446 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_446, 0, x_445);
x_447 = l_Lean_MessageData_ofFormat(x_446);
x_448 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_440)) {
 x_449 = lean_alloc_ctor(7, 2, 0);
} else {
 x_449 = x_440;
 lean_ctor_set_tag(x_449, 7);
}
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_447);
x_450 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
if (lean_is_scalar(x_433)) {
 x_451 = lean_alloc_ctor(7, 2, 0);
} else {
 x_451 = x_433;
 lean_ctor_set_tag(x_451, 7);
}
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
x_452 = l_Lean_MessageData_ofExpr(x_436);
x_453 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
x_454 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_454);
lean_ctor_set(x_13, 0, x_453);
x_455 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_425, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_443);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_425, x_1, x_360, x_456, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_457);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_456);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_440);
lean_dec(x_436);
lean_dec(x_433);
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_459 = lean_ctor_get(x_441, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_441, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_461 = x_441;
} else {
 lean_dec_ref(x_441);
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
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_433);
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_463 = lean_ctor_get(x_434, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_434, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_465 = x_434;
} else {
 lean_dec_ref(x_434);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_464);
return x_466;
}
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_467 = lean_ctor_get(x_423, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_423, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_469 = x_423;
} else {
 lean_dec_ref(x_423);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 2, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_468);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_360);
lean_free_object(x_13);
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
x_471 = lean_ctor_get(x_420, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_420, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_473 = x_420;
} else {
 lean_dec_ref(x_420);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
else
{
size_t x_475; size_t x_476; lean_object* x_477; lean_object* x_478; 
x_475 = 0;
x_476 = lean_usize_of_nat(x_361);
lean_dec(x_361);
x_477 = lean_box(0);
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
x_478 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(x_1, x_2, x_359, x_475, x_476, x_477, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_359);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec(x_478);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_480 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_479);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
lean_dec(x_480);
x_482 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_360);
x_483 = lean_grind_internalize(x_360, x_2, x_482, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_481);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
lean_dec(x_483);
x_485 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_486 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_485, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_484);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_unbox(x_487);
lean_dec(x_487);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; 
lean_free_object(x_13);
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
lean_dec(x_486);
x_490 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_485, x_1, x_360, x_477, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_489);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_486, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_492 = x_486;
} else {
 lean_dec_ref(x_486);
 x_492 = lean_box(0);
}
x_493 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_491);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_495 = l_Lean_Expr_getAppFn(x_360);
x_496 = lean_st_ref_get(x_3, x_494);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_499 = x_496;
} else {
 lean_dec_ref(x_496);
 x_499 = lean_box(0);
}
lean_inc(x_495);
x_500 = l_Lean_Meta_Grind_Goal_getENode(x_497, x_495, x_9, x_10, x_498);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_ctor_get(x_501, 7);
lean_inc(x_503);
lean_dec(x_501);
x_504 = l___private_Init_Data_Repr_0__Nat_reprFast(x_503);
x_505 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_505, 0, x_504);
x_506 = l_Lean_MessageData_ofFormat(x_505);
x_507 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_499)) {
 x_508 = lean_alloc_ctor(7, 2, 0);
} else {
 x_508 = x_499;
 lean_ctor_set_tag(x_508, 7);
}
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_506);
x_509 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
if (lean_is_scalar(x_492)) {
 x_510 = lean_alloc_ctor(7, 2, 0);
} else {
 x_510 = x_492;
 lean_ctor_set_tag(x_510, 7);
}
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
x_511 = l_Lean_MessageData_ofExpr(x_495);
x_512 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
x_513 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_513);
lean_ctor_set(x_13, 0, x_512);
x_514 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_485, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_502);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_485, x_1, x_360, x_515, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_516);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_515);
return x_517;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_499);
lean_dec(x_495);
lean_dec(x_492);
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_518 = lean_ctor_get(x_500, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_500, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_520 = x_500;
} else {
 lean_dec_ref(x_500);
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
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_492);
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_522 = lean_ctor_get(x_493, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_493, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_524 = x_493;
} else {
 lean_dec_ref(x_493);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_523);
return x_525;
}
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_360);
lean_free_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_526 = lean_ctor_get(x_483, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_483, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_528 = x_483;
} else {
 lean_dec_ref(x_483);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 2, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_526);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_360);
lean_free_object(x_13);
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
x_530 = lean_ctor_get(x_480, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_480, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_532 = x_480;
} else {
 lean_dec_ref(x_480);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_531);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_360);
lean_free_object(x_13);
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
x_534 = lean_ctor_get(x_478, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_478, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_536 = x_478;
} else {
 lean_dec_ref(x_478);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_535);
return x_537;
}
}
}
}
}
else
{
uint8_t x_538; 
lean_free_object(x_13);
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
x_538 = !lean_is_exclusive(x_17);
if (x_538 == 0)
{
return x_17;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_17, 0);
x_540 = lean_ctor_get(x_17, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_17);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
}
else
{
lean_object* x_542; lean_object* x_543; 
x_542 = lean_ctor_get(x_13, 1);
lean_inc(x_542);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_543 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_542);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_ctor_get(x_544, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_544, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_548 = x_544;
} else {
 lean_dec_ref(x_544);
 x_548 = lean_box(0);
}
x_549 = lean_array_get_size(x_546);
x_550 = lean_unsigned_to_nat(0u);
x_551 = lean_nat_dec_lt(x_550, x_549);
if (x_551 == 0)
{
lean_object* x_552; 
lean_dec(x_549);
lean_dec(x_546);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_552 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_545);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
lean_dec(x_552);
x_554 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_547);
x_555 = lean_grind_internalize(x_547, x_2, x_554, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_553);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; 
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
lean_dec(x_555);
x_557 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_558 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_557, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_556);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_unbox(x_559);
lean_dec(x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_548);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_dec(x_558);
x_562 = lean_box(0);
x_563 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_557, x_1, x_547, x_562, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_561);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_558, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_565 = x_558;
} else {
 lean_dec_ref(x_558);
 x_565 = lean_box(0);
}
x_566 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_564);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
lean_dec(x_566);
x_568 = l_Lean_Expr_getAppFn(x_547);
x_569 = lean_st_ref_get(x_3, x_567);
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_572 = x_569;
} else {
 lean_dec_ref(x_569);
 x_572 = lean_box(0);
}
lean_inc(x_568);
x_573 = l_Lean_Meta_Grind_Goal_getENode(x_570, x_568, x_9, x_10, x_571);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_ctor_get(x_574, 7);
lean_inc(x_576);
lean_dec(x_574);
x_577 = l___private_Init_Data_Repr_0__Nat_reprFast(x_576);
x_578 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_578, 0, x_577);
x_579 = l_Lean_MessageData_ofFormat(x_578);
x_580 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_572)) {
 x_581 = lean_alloc_ctor(7, 2, 0);
} else {
 x_581 = x_572;
 lean_ctor_set_tag(x_581, 7);
}
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_579);
x_582 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
if (lean_is_scalar(x_565)) {
 x_583 = lean_alloc_ctor(7, 2, 0);
} else {
 x_583 = x_565;
 lean_ctor_set_tag(x_583, 7);
}
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
x_584 = l_Lean_MessageData_ofExpr(x_568);
if (lean_is_scalar(x_548)) {
 x_585 = lean_alloc_ctor(7, 2, 0);
} else {
 x_585 = x_548;
 lean_ctor_set_tag(x_585, 7);
}
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
x_586 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_587 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
x_588 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_557, x_587, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_575);
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
lean_dec(x_588);
x_591 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_557, x_1, x_547, x_589, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_590);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_589);
return x_591;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_572);
lean_dec(x_568);
lean_dec(x_565);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_592 = lean_ctor_get(x_573, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_573, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_594 = x_573;
} else {
 lean_dec_ref(x_573);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
return x_595;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_565);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_596 = lean_ctor_get(x_566, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_566, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_598 = x_566;
} else {
 lean_dec_ref(x_566);
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
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_600 = lean_ctor_get(x_555, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_555, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_602 = x_555;
} else {
 lean_dec_ref(x_555);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_548);
lean_dec(x_547);
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
x_604 = lean_ctor_get(x_552, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_552, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_606 = x_552;
} else {
 lean_dec_ref(x_552);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
else
{
uint8_t x_608; 
x_608 = lean_nat_dec_le(x_549, x_549);
if (x_608 == 0)
{
lean_object* x_609; 
lean_dec(x_549);
lean_dec(x_546);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_609 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_545);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_611 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_547);
x_612 = lean_grind_internalize(x_547, x_2, x_611, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_610);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
x_614 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_615 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_614, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_613);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_unbox(x_616);
lean_dec(x_616);
if (x_617 == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_548);
x_618 = lean_ctor_get(x_615, 1);
lean_inc(x_618);
lean_dec(x_615);
x_619 = lean_box(0);
x_620 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_614, x_1, x_547, x_619, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_618);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_620;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_615, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_622 = x_615;
} else {
 lean_dec_ref(x_615);
 x_622 = lean_box(0);
}
x_623 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_621);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
lean_dec(x_623);
x_625 = l_Lean_Expr_getAppFn(x_547);
x_626 = lean_st_ref_get(x_3, x_624);
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_626)) {
 lean_ctor_release(x_626, 0);
 lean_ctor_release(x_626, 1);
 x_629 = x_626;
} else {
 lean_dec_ref(x_626);
 x_629 = lean_box(0);
}
lean_inc(x_625);
x_630 = l_Lean_Meta_Grind_Goal_getENode(x_627, x_625, x_9, x_10, x_628);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
lean_dec(x_630);
x_633 = lean_ctor_get(x_631, 7);
lean_inc(x_633);
lean_dec(x_631);
x_634 = l___private_Init_Data_Repr_0__Nat_reprFast(x_633);
x_635 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_635, 0, x_634);
x_636 = l_Lean_MessageData_ofFormat(x_635);
x_637 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_629)) {
 x_638 = lean_alloc_ctor(7, 2, 0);
} else {
 x_638 = x_629;
 lean_ctor_set_tag(x_638, 7);
}
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_636);
x_639 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
if (lean_is_scalar(x_622)) {
 x_640 = lean_alloc_ctor(7, 2, 0);
} else {
 x_640 = x_622;
 lean_ctor_set_tag(x_640, 7);
}
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
x_641 = l_Lean_MessageData_ofExpr(x_625);
if (lean_is_scalar(x_548)) {
 x_642 = lean_alloc_ctor(7, 2, 0);
} else {
 x_642 = x_548;
 lean_ctor_set_tag(x_642, 7);
}
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
x_643 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_644 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set(x_644, 1, x_643);
x_645 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_614, x_644, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_632);
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_648 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_614, x_1, x_547, x_646, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_647);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_646);
return x_648;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_629);
lean_dec(x_625);
lean_dec(x_622);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_649 = lean_ctor_get(x_630, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_630, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 x_651 = x_630;
} else {
 lean_dec_ref(x_630);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_622);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_653 = lean_ctor_get(x_623, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_623, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_655 = x_623;
} else {
 lean_dec_ref(x_623);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_657 = lean_ctor_get(x_612, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_612, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_659 = x_612;
} else {
 lean_dec_ref(x_612);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_658);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_548);
lean_dec(x_547);
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
x_661 = lean_ctor_get(x_609, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_609, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_663 = x_609;
} else {
 lean_dec_ref(x_609);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
else
{
size_t x_665; size_t x_666; lean_object* x_667; lean_object* x_668; 
x_665 = 0;
x_666 = lean_usize_of_nat(x_549);
lean_dec(x_549);
x_667 = lean_box(0);
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
x_668 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(x_1, x_2, x_546, x_665, x_666, x_667, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_545);
lean_dec(x_546);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; 
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
lean_dec(x_668);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_670 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_669);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
lean_dec(x_670);
x_672 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_547);
x_673 = lean_grind_internalize(x_547, x_2, x_672, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_671);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; 
x_674 = lean_ctor_get(x_673, 1);
lean_inc(x_674);
lean_dec(x_673);
x_675 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3;
x_676 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_675, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_674);
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_unbox(x_677);
lean_dec(x_677);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_548);
x_679 = lean_ctor_get(x_676, 1);
lean_inc(x_679);
lean_dec(x_676);
x_680 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_675, x_1, x_547, x_667, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_679);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_680;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_676, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_682 = x_676;
} else {
 lean_dec_ref(x_676);
 x_682 = lean_box(0);
}
x_683 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_681);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_684 = lean_ctor_get(x_683, 1);
lean_inc(x_684);
lean_dec(x_683);
x_685 = l_Lean_Expr_getAppFn(x_547);
x_686 = lean_st_ref_get(x_3, x_684);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
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
lean_inc(x_685);
x_690 = l_Lean_Meta_Grind_Goal_getENode(x_687, x_685, x_9, x_10, x_688);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
x_693 = lean_ctor_get(x_691, 7);
lean_inc(x_693);
lean_dec(x_691);
x_694 = l___private_Init_Data_Repr_0__Nat_reprFast(x_693);
x_695 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_695, 0, x_694);
x_696 = l_Lean_MessageData_ofFormat(x_695);
x_697 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5;
if (lean_is_scalar(x_689)) {
 x_698 = lean_alloc_ctor(7, 2, 0);
} else {
 x_698 = x_689;
 lean_ctor_set_tag(x_698, 7);
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_696);
x_699 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7;
if (lean_is_scalar(x_682)) {
 x_700 = lean_alloc_ctor(7, 2, 0);
} else {
 x_700 = x_682;
 lean_ctor_set_tag(x_700, 7);
}
lean_ctor_set(x_700, 0, x_698);
lean_ctor_set(x_700, 1, x_699);
x_701 = l_Lean_MessageData_ofExpr(x_685);
if (lean_is_scalar(x_548)) {
 x_702 = lean_alloc_ctor(7, 2, 0);
} else {
 x_702 = x_548;
 lean_ctor_set_tag(x_702, 7);
}
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
x_703 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_704 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
x_705 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_675, x_704, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_692);
x_706 = lean_ctor_get(x_705, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_705, 1);
lean_inc(x_707);
lean_dec(x_705);
x_708 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_675, x_1, x_547, x_706, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_707);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_706);
return x_708;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_689);
lean_dec(x_685);
lean_dec(x_682);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_709 = lean_ctor_get(x_690, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_690, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_711 = x_690;
} else {
 lean_dec_ref(x_690);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_709);
lean_ctor_set(x_712, 1, x_710);
return x_712;
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_682);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_713 = lean_ctor_get(x_683, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_683, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_715 = x_683;
} else {
 lean_dec_ref(x_683);
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
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_717 = lean_ctor_get(x_673, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_673, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_719 = x_673;
} else {
 lean_dec_ref(x_673);
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
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_548);
lean_dec(x_547);
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
x_721 = lean_ctor_get(x_670, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_670, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_723 = x_670;
} else {
 lean_dec_ref(x_670);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_721);
lean_ctor_set(x_724, 1, x_722);
return x_724;
}
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_548);
lean_dec(x_547);
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
x_725 = lean_ctor_get(x_668, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_668, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_727 = x_668;
} else {
 lean_dec_ref(x_668);
 x_727 = lean_box(0);
}
if (lean_is_scalar(x_727)) {
 x_728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_728 = x_727;
}
lean_ctor_set(x_728, 0, x_725);
lean_ctor_set(x_728, 1, x_726);
return x_728;
}
}
}
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
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
x_729 = lean_ctor_get(x_543, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_543, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 lean_ctor_release(x_543, 1);
 x_731 = x_543;
} else {
 lean_dec_ref(x_543);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(1, 2, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_729);
lean_ctor_set(x_732, 1, x_730);
return x_732;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = l_List_reverse___rarg(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(x_16, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_19);
{
lean_object* _tmp_1 = x_17;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_11 = x_20;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_2);
lean_dec(x_17);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_28 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(x_26, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_3);
x_2 = x_27;
x_3 = x_31;
x_12 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
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
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 11);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 11);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 3);
x_20 = l_Lean_PersistentArray_push___rarg(x_19, x_1);
lean_ctor_set(x_14, 3, x_20);
x_21 = lean_st_ref_set(x_3, x_13, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_14, 2);
x_31 = lean_ctor_get(x_14, 4);
x_32 = lean_ctor_get(x_14, 5);
x_33 = lean_ctor_get(x_14, 6);
x_34 = lean_ctor_get(x_14, 7);
x_35 = lean_ctor_get(x_14, 8);
x_36 = lean_ctor_get(x_14, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_36);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_37 = l_Lean_PersistentArray_push___rarg(x_36, x_1);
x_38 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_31);
lean_ctor_set(x_38, 5, x_32);
lean_ctor_set(x_38, 6, x_33);
lean_ctor_set(x_38, 7, x_34);
lean_ctor_set(x_38, 8, x_35);
lean_ctor_set(x_13, 11, x_38);
x_39 = lean_st_ref_set(x_3, x_13, x_15);
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
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
x_46 = lean_ctor_get(x_13, 2);
x_47 = lean_ctor_get(x_13, 3);
x_48 = lean_ctor_get(x_13, 4);
x_49 = lean_ctor_get(x_13, 5);
x_50 = lean_ctor_get(x_13, 6);
x_51 = lean_ctor_get_uint8(x_13, sizeof(void*)*15);
x_52 = lean_ctor_get(x_13, 7);
x_53 = lean_ctor_get(x_13, 8);
x_54 = lean_ctor_get(x_13, 9);
x_55 = lean_ctor_get(x_13, 10);
x_56 = lean_ctor_get(x_13, 12);
x_57 = lean_ctor_get(x_13, 13);
x_58 = lean_ctor_get(x_13, 14);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_59 = lean_ctor_get(x_14, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_14, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_14, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_14, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_14, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_14, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_14, 3);
lean_inc(x_67);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 lean_ctor_release(x_14, 6);
 lean_ctor_release(x_14, 7);
 lean_ctor_release(x_14, 8);
 x_68 = x_14;
} else {
 lean_dec_ref(x_14);
 x_68 = lean_box(0);
}
x_69 = l_Lean_PersistentArray_push___rarg(x_67, x_1);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 9, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_60);
lean_ctor_set(x_70, 2, x_61);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_70, 4, x_62);
lean_ctor_set(x_70, 5, x_63);
lean_ctor_set(x_70, 6, x_64);
lean_ctor_set(x_70, 7, x_65);
lean_ctor_set(x_70, 8, x_66);
x_71 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_71, 0, x_44);
lean_ctor_set(x_71, 1, x_45);
lean_ctor_set(x_71, 2, x_46);
lean_ctor_set(x_71, 3, x_47);
lean_ctor_set(x_71, 4, x_48);
lean_ctor_set(x_71, 5, x_49);
lean_ctor_set(x_71, 6, x_50);
lean_ctor_set(x_71, 7, x_52);
lean_ctor_set(x_71, 8, x_53);
lean_ctor_set(x_71, 9, x_54);
lean_ctor_set(x_71, 10, x_55);
lean_ctor_set(x_71, 11, x_70);
lean_ctor_set(x_71, 12, x_56);
lean_ctor_set(x_71, 13, x_57);
lean_ctor_set(x_71, 14, x_58);
lean_ctor_set_uint8(x_71, sizeof(void*)*15, x_51);
x_72 = lean_st_ref_set(x_3, x_71, x_15);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ematch", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_activateTheorem___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("activated `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_activateTheorem___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`, ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_activateTheorem___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
x_19 = l_Lean_Meta_Grind_shareCommon(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(x_2, x_16, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_25);
lean_ctor_set(x_1, 3, x_25);
lean_ctor_set(x_1, 1, x_21);
x_27 = l_Lean_Meta_Grind_activateTheorem___closed__2;
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_18);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_Grind_Origin_key(x_18);
lean_dec(x_18);
x_40 = l_Lean_MessageData_ofName(x_39);
x_41 = l_Lean_Meta_Grind_activateTheorem___closed__4;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_40);
lean_ctor_set(x_28, 0, x_41);
x_42 = l_Lean_Meta_Grind_activateTheorem___closed__6;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_42);
lean_ctor_set(x_19, 0, x_28);
x_43 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_25, x_23);
x_44 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_43, x_23);
x_45 = l_Lean_MessageData_ofList(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_27, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_50);
return x_52;
}
else
{
uint8_t x_53; 
lean_free_object(x_28);
lean_dec(x_1);
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
return x_37;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_28, 1);
lean_inc(x_57);
lean_dec(x_28);
x_58 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Meta_Grind_Origin_key(x_18);
lean_dec(x_18);
x_61 = l_Lean_MessageData_ofName(x_60);
x_62 = l_Lean_Meta_Grind_activateTheorem___closed__4;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_Grind_activateTheorem___closed__6;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_64);
lean_ctor_set(x_19, 0, x_63);
x_65 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_25, x_23);
x_66 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_65, x_23);
x_67 = l_Lean_MessageData_ofList(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_19);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_27, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_58, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_58, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_77 = x_58;
} else {
 lean_dec_ref(x_58);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_19);
lean_dec(x_21);
lean_free_object(x_1);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_24);
if (x_79 == 0)
{
return x_24;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_24, 0);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_24);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_19, 0);
x_84 = lean_ctor_get(x_19, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_19);
x_85 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_86 = l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(x_2, x_16, x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_18);
lean_inc(x_87);
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 1, x_83);
x_89 = l_Lean_Meta_Grind_activateTheorem___closed__2;
x_90 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_87);
lean_dec(x_18);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_box(0);
x_95 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Meta_Grind_Origin_key(x_18);
lean_dec(x_18);
x_101 = l_Lean_MessageData_ofName(x_100);
x_102 = l_Lean_Meta_Grind_activateTheorem___closed__4;
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(7, 2, 0);
} else {
 x_103 = x_97;
 lean_ctor_set_tag(x_103, 7);
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Meta_Grind_activateTheorem___closed__6;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_87, x_85);
x_107 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_106, x_85);
x_108 = l_Lean_MessageData_ofList(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_89, x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_114);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_97);
lean_dec(x_1);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_98, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_98, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_118 = x_98;
} else {
 lean_dec_ref(x_98);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_83);
lean_free_object(x_1);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_86, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_86, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_122 = x_86;
} else {
 lean_dec_ref(x_86);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_124 = lean_ctor_get(x_1, 0);
x_125 = lean_ctor_get(x_1, 1);
x_126 = lean_ctor_get(x_1, 2);
x_127 = lean_ctor_get(x_1, 3);
x_128 = lean_ctor_get(x_1, 4);
x_129 = lean_ctor_get(x_1, 5);
x_130 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_1);
x_131 = l_Lean_Meta_Grind_shareCommon(x_125, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_136 = l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(x_2, x_127, x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_129);
lean_inc(x_137);
x_139 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_139, 0, x_124);
lean_ctor_set(x_139, 1, x_132);
lean_ctor_set(x_139, 2, x_126);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_128);
lean_ctor_set(x_139, 5, x_129);
lean_ctor_set_uint8(x_139, sizeof(void*)*6, x_130);
x_140 = l_Lean_Meta_Grind_activateTheorem___closed__2;
x_141 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_140, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_138);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_129);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_box(0);
x_146 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_139, x_145, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_148 = x_141;
} else {
 lean_dec_ref(x_141);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_147);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = l_Lean_Meta_Grind_Origin_key(x_129);
lean_dec(x_129);
x_152 = l_Lean_MessageData_ofName(x_151);
x_153 = l_Lean_Meta_Grind_activateTheorem___closed__4;
if (lean_is_scalar(x_148)) {
 x_154 = lean_alloc_ctor(7, 2, 0);
} else {
 x_154 = x_148;
 lean_ctor_set_tag(x_154, 7);
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Meta_Grind_activateTheorem___closed__6;
if (lean_is_scalar(x_134)) {
 x_156 = lean_alloc_ctor(7, 2, 0);
} else {
 x_156 = x_134;
 lean_ctor_set_tag(x_156, 7);
}
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_137, x_135);
x_158 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_157, x_135);
x_159 = l_Lean_MessageData_ofList(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_140, x_162, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_150);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_139, x_164, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_165);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_148);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_129);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_167 = lean_ctor_get(x_149, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_149, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_169 = x_149;
} else {
 lean_dec_ref(x_149);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_171 = lean_ctor_get(x_136, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_136, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_173 = x_136;
} else {
 lean_dec_ref(x_136);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_is_matcher(x_14, x_1);
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
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_is_matcher(x_19, x_1);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
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
lean_dec(x_8);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_7);
x_19 = lean_array_uget(x_4, x_6);
x_20 = 0;
x_21 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_22 = l_Lean_Meta_Grind_mkEMatchEqTheorem(x_19, x_20, x_21, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_25 = l_Lean_Meta_Grind_activateTheorem(x_23, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_29 = lean_box(0);
x_6 = x_28;
x_7 = x_29;
x_16 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 6);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_14, sizeof(void*)*15);
x_24 = lean_ctor_get(x_14, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 8);
lean_inc(x_25);
x_26 = lean_ctor_get(x_14, 9);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 10);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 11);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 7);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 8);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_box(0);
lean_inc(x_1);
x_39 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_37, x_1, x_38);
x_40 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_32);
lean_ctor_set(x_40, 4, x_33);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set(x_40, 6, x_35);
lean_ctor_set(x_40, 7, x_36);
lean_ctor_set(x_40, 8, x_39);
x_41 = lean_ctor_get(x_14, 12);
lean_inc(x_41);
x_42 = lean_ctor_get(x_14, 13);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 14);
lean_inc(x_43);
lean_dec(x_14);
x_44 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 2, x_18);
lean_ctor_set(x_44, 3, x_19);
lean_ctor_set(x_44, 4, x_20);
lean_ctor_set(x_44, 5, x_21);
lean_ctor_set(x_44, 6, x_22);
lean_ctor_set(x_44, 7, x_24);
lean_ctor_set(x_44, 8, x_25);
lean_ctor_set(x_44, 9, x_26);
lean_ctor_set(x_44, 10, x_27);
lean_ctor_set(x_44, 11, x_40);
lean_ctor_set(x_44, 12, x_41);
lean_ctor_set(x_44, 13, x_42);
lean_ctor_set(x_44, 14, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*15, x_23);
x_45 = lean_st_ref_set(x_4, x_44, x_15);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_47 = lean_get_match_equations_for(x_1, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_array_size(x_51);
x_53 = 0;
x_54 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(x_2, x_50, x_51, x_51, x_52, x_53, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_49);
lean_dec(x_51);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_38);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_47);
if (x_63 == 0)
{
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_47, 0);
x_65 = lean_ctor_get(x_47, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_47);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 11);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 8);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_18, x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_13);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_21;
}
else
{
lean_object* x_22; 
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
x_22 = lean_box(0);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 11);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 8);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_26, x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(x_1, x_2, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
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
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_13);
x_14 = l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(x_13, x_2, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
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
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_getConfig___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*6 + 1);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
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
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(x_1, x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_5, x_9);
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
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_HeadIndex_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(x_1, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(x_1, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Lean_Meta_Grind_EMatchTheorems_insert(x_17, x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_18);
x_21 = lean_st_ref_set(x_3, x_13, x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_16, 1);
x_29 = lean_ctor_get(x_16, 2);
x_30 = lean_ctor_get(x_16, 3);
x_31 = lean_ctor_get(x_16, 4);
x_32 = lean_ctor_get(x_16, 5);
x_33 = lean_ctor_get(x_16, 6);
x_34 = lean_ctor_get(x_16, 7);
x_35 = lean_ctor_get(x_16, 8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_30);
lean_ctor_set(x_36, 4, x_31);
lean_ctor_set(x_36, 5, x_32);
lean_ctor_set(x_36, 6, x_33);
lean_ctor_set(x_36, 7, x_34);
lean_ctor_set(x_36, 8, x_35);
lean_ctor_set(x_13, 11, x_36);
x_37 = lean_st_ref_set(x_3, x_13, x_14);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
x_44 = lean_ctor_get(x_13, 2);
x_45 = lean_ctor_get(x_13, 3);
x_46 = lean_ctor_get(x_13, 4);
x_47 = lean_ctor_get(x_13, 5);
x_48 = lean_ctor_get(x_13, 6);
x_49 = lean_ctor_get_uint8(x_13, sizeof(void*)*15);
x_50 = lean_ctor_get(x_13, 7);
x_51 = lean_ctor_get(x_13, 8);
x_52 = lean_ctor_get(x_13, 9);
x_53 = lean_ctor_get(x_13, 10);
x_54 = lean_ctor_get(x_13, 11);
x_55 = lean_ctor_get(x_13, 12);
x_56 = lean_ctor_get(x_13, 13);
x_57 = lean_ctor_get(x_13, 14);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = l_Lean_Meta_Grind_EMatchTheorems_insert(x_58, x_1);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_54, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_54, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 7);
lean_inc(x_66);
x_67 = lean_ctor_get(x_54, 8);
lean_inc(x_67);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 lean_ctor_release(x_54, 6);
 lean_ctor_release(x_54, 7);
 lean_ctor_release(x_54, 8);
 x_68 = x_54;
} else {
 lean_dec_ref(x_54);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 9, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_60);
lean_ctor_set(x_69, 2, x_61);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_63);
lean_ctor_set(x_69, 5, x_64);
lean_ctor_set(x_69, 6, x_65);
lean_ctor_set(x_69, 7, x_66);
lean_ctor_set(x_69, 8, x_67);
x_70 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_70, 0, x_42);
lean_ctor_set(x_70, 1, x_43);
lean_ctor_set(x_70, 2, x_44);
lean_ctor_set(x_70, 3, x_45);
lean_ctor_set(x_70, 4, x_46);
lean_ctor_set(x_70, 5, x_47);
lean_ctor_set(x_70, 6, x_48);
lean_ctor_set(x_70, 7, x_50);
lean_ctor_set(x_70, 8, x_51);
lean_ctor_set(x_70, 9, x_52);
lean_ctor_set(x_70, 10, x_53);
lean_ctor_set(x_70, 11, x_69);
lean_ctor_set(x_70, 12, x_55);
lean_ctor_set(x_70, 13, x_56);
lean_ctor_set(x_70, 14, x_57);
lean_ctor_set_uint8(x_70, sizeof(void*)*15, x_49);
x_71 = lean_st_ref_set(x_3, x_70, x_14);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reinsert `", 10, 10);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_7);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_26 = lean_st_ref_get(x_9, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 11);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
x_34 = lean_ctor_get(x_19, 2);
x_35 = lean_ctor_get(x_19, 3);
x_36 = lean_ctor_get(x_19, 4);
x_37 = lean_ctor_get(x_19, 5);
x_38 = l_Lean_Meta_Grind_EMatchTheorems_isErased(x_30, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
lean_inc(x_3);
x_40 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(x_3, x_36, x_39);
lean_inc(x_37);
lean_inc(x_40);
lean_ctor_set(x_19, 4, x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_41 = l_Lean_Meta_Grind_activateTheorem(x_19, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_43;
x_22 = x_42;
goto block_25;
}
else
{
uint8_t x_44; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_40, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
x_51 = l_Lean_Meta_Grind_activateTheorem___closed__2;
x_52 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_51, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_40);
lean_dec(x_37);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_box(0);
x_57 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_56, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_21 = x_58;
x_22 = x_59;
goto block_25;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_52, 1);
x_62 = lean_ctor_get(x_52, 0);
lean_dec(x_62);
x_63 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Meta_Grind_Origin_key(x_37);
lean_dec(x_37);
x_66 = l_Lean_MessageData_ofName(x_65);
x_67 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_66);
lean_ctor_set(x_52, 0, x_67);
x_68 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_68);
lean_ctor_set(x_40, 0, x_52);
x_69 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_51, x_40, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_64);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_70, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_71);
lean_dec(x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_21 = x_73;
x_22 = x_74;
goto block_25;
}
else
{
uint8_t x_75; 
lean_free_object(x_52);
lean_free_object(x_40);
lean_dec(x_19);
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_63);
if (x_75 == 0)
{
return x_63;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_63, 0);
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_63);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_52, 1);
lean_inc(x_79);
lean_dec(x_52);
x_80 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_Meta_Grind_Origin_key(x_37);
lean_dec(x_37);
x_83 = l_Lean_MessageData_ofName(x_82);
x_84 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_86);
lean_ctor_set(x_40, 0, x_85);
x_87 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_51, x_40, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_81);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_88, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_89);
lean_dec(x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_21 = x_91;
x_22 = x_92;
goto block_25;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_40);
lean_dec(x_19);
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_95 = x_80;
} else {
 lean_dec_ref(x_80);
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
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_40);
x_97 = l_Lean_Meta_Grind_activateTheorem___closed__2;
x_98 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_97, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_37);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_box(0);
x_103 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_102, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_21 = x_104;
x_22 = x_105;
goto block_25;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_107 = x_98;
} else {
 lean_dec_ref(x_98);
 x_107 = lean_box(0);
}
x_108 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lean_Meta_Grind_Origin_key(x_37);
lean_dec(x_37);
x_111 = l_Lean_MessageData_ofName(x_110);
x_112 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
if (lean_is_scalar(x_107)) {
 x_113 = lean_alloc_ctor(7, 2, 0);
} else {
 x_113 = x_107;
 lean_ctor_set_tag(x_113, 7);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_97, x_115, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_109);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_117, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_118);
lean_dec(x_117);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_21 = x_120;
x_22 = x_121;
goto block_25;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_107);
lean_dec(x_19);
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_122 = lean_ctor_get(x_108, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_124 = x_108;
} else {
 lean_dec_ref(x_108);
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
}
}
}
else
{
lean_object* x_126; 
lean_free_object(x_19);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_126 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_126;
x_22 = x_28;
goto block_25;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; 
x_127 = lean_ctor_get(x_19, 0);
x_128 = lean_ctor_get(x_19, 1);
x_129 = lean_ctor_get(x_19, 2);
x_130 = lean_ctor_get(x_19, 3);
x_131 = lean_ctor_get(x_19, 4);
x_132 = lean_ctor_get(x_19, 5);
x_133 = lean_ctor_get_uint8(x_19, sizeof(void*)*6);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_19);
x_134 = l_Lean_Meta_Grind_EMatchTheorems_isErased(x_30, x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_box(0);
lean_inc(x_3);
x_136 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(x_3, x_131, x_135);
lean_inc(x_132);
lean_inc(x_136);
x_137 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_128);
lean_ctor_set(x_137, 2, x_129);
lean_ctor_set(x_137, 3, x_130);
lean_ctor_set(x_137, 4, x_136);
lean_ctor_set(x_137, 5, x_132);
lean_ctor_set_uint8(x_137, sizeof(void*)*6, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_138; 
lean_dec(x_132);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_138 = l_Lean_Meta_Grind_activateTheorem(x_137, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_140;
x_22 = x_139;
goto block_25;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_143 = x_138;
} else {
 lean_dec_ref(x_138);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_145 = x_136;
} else {
 lean_dec_ref(x_136);
 x_145 = lean_box(0);
}
x_146 = l_Lean_Meta_Grind_activateTheorem___closed__2;
x_147 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_146, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_145);
lean_dec(x_132);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_box(0);
x_152 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_137, x_151, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_21 = x_153;
x_22 = x_154;
goto block_25;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_147, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_156 = x_147;
} else {
 lean_dec_ref(x_147);
 x_156 = lean_box(0);
}
x_157 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_155);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = l_Lean_Meta_Grind_Origin_key(x_132);
lean_dec(x_132);
x_160 = l_Lean_MessageData_ofName(x_159);
x_161 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
if (lean_is_scalar(x_156)) {
 x_162 = lean_alloc_ctor(7, 2, 0);
} else {
 x_162 = x_156;
 lean_ctor_set_tag(x_162, 7);
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
if (lean_is_scalar(x_145)) {
 x_164 = lean_alloc_ctor(7, 2, 0);
} else {
 x_164 = x_145;
 lean_ctor_set_tag(x_164, 7);
}
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_146, x_164, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_158);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_137, x_166, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_167);
lean_dec(x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_21 = x_169;
x_22 = x_170;
goto block_25;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_156);
lean_dec(x_145);
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_171 = lean_ctor_get(x_157, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_157, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_173 = x_157;
} else {
 lean_dec_ref(x_157);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_175 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_175;
x_22 = x_28;
goto block_25;
}
}
block_25:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_6 = x_20;
x_7 = x_23;
x_8 = lean_box(0);
x_17 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 11);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 2);
x_23 = lean_ctor_get(x_15, 3);
lean_inc(x_20);
x_24 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(x_20, x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_free_object(x_15);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_12);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(x_20, x_1);
lean_ctor_set(x_15, 0, x_27);
x_28 = lean_st_ref_take(x_3, x_17);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 11);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 11);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
lean_ctor_set(x_30, 0, x_15);
x_36 = lean_st_ref_set(x_3, x_29, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_3, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 5);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = lean_box(0);
lean_inc(x_26);
x_44 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_26, x_41, x_42, x_26, x_26, x_43, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_26);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_53 = lean_ctor_get(x_30, 1);
x_54 = lean_ctor_get(x_30, 2);
x_55 = lean_ctor_get(x_30, 3);
x_56 = lean_ctor_get(x_30, 4);
x_57 = lean_ctor_get(x_30, 5);
x_58 = lean_ctor_get(x_30, 6);
x_59 = lean_ctor_get(x_30, 7);
x_60 = lean_ctor_get(x_30, 8);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_30);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_15);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_55);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set(x_61, 5, x_57);
lean_ctor_set(x_61, 6, x_58);
lean_ctor_set(x_61, 7, x_59);
lean_ctor_set(x_61, 8, x_60);
lean_ctor_set(x_29, 11, x_61);
x_62 = lean_st_ref_set(x_3, x_29, x_31);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_get(x_3, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 5);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_box(0);
x_69 = lean_box(0);
lean_inc(x_26);
x_70 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_26, x_67, x_68, x_26, x_26, x_69, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_26);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_78 = lean_ctor_get(x_29, 0);
x_79 = lean_ctor_get(x_29, 1);
x_80 = lean_ctor_get(x_29, 2);
x_81 = lean_ctor_get(x_29, 3);
x_82 = lean_ctor_get(x_29, 4);
x_83 = lean_ctor_get(x_29, 5);
x_84 = lean_ctor_get(x_29, 6);
x_85 = lean_ctor_get_uint8(x_29, sizeof(void*)*15);
x_86 = lean_ctor_get(x_29, 7);
x_87 = lean_ctor_get(x_29, 8);
x_88 = lean_ctor_get(x_29, 9);
x_89 = lean_ctor_get(x_29, 10);
x_90 = lean_ctor_get(x_29, 12);
x_91 = lean_ctor_get(x_29, 13);
x_92 = lean_ctor_get(x_29, 14);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_29);
x_93 = lean_ctor_get(x_30, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_30, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_30, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_30, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_30, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_30, 6);
lean_inc(x_98);
x_99 = lean_ctor_get(x_30, 7);
lean_inc(x_99);
x_100 = lean_ctor_get(x_30, 8);
lean_inc(x_100);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 lean_ctor_release(x_30, 6);
 lean_ctor_release(x_30, 7);
 lean_ctor_release(x_30, 8);
 x_101 = x_30;
} else {
 lean_dec_ref(x_30);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 9, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_15);
lean_ctor_set(x_102, 1, x_93);
lean_ctor_set(x_102, 2, x_94);
lean_ctor_set(x_102, 3, x_95);
lean_ctor_set(x_102, 4, x_96);
lean_ctor_set(x_102, 5, x_97);
lean_ctor_set(x_102, 6, x_98);
lean_ctor_set(x_102, 7, x_99);
lean_ctor_set(x_102, 8, x_100);
x_103 = lean_alloc_ctor(0, 15, 1);
lean_ctor_set(x_103, 0, x_78);
lean_ctor_set(x_103, 1, x_79);
lean_ctor_set(x_103, 2, x_80);
lean_ctor_set(x_103, 3, x_81);
lean_ctor_set(x_103, 4, x_82);
lean_ctor_set(x_103, 5, x_83);
lean_ctor_set(x_103, 6, x_84);
lean_ctor_set(x_103, 7, x_86);
lean_ctor_set(x_103, 8, x_87);
lean_ctor_set(x_103, 9, x_88);
lean_ctor_set(x_103, 10, x_89);
lean_ctor_set(x_103, 11, x_102);
lean_ctor_set(x_103, 12, x_90);
lean_ctor_set(x_103, 13, x_91);
lean_ctor_set(x_103, 14, x_92);
lean_ctor_set_uint8(x_103, sizeof(void*)*15, x_85);
x_104 = lean_st_ref_set(x_3, x_103, x_31);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_get(x_3, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 5);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_box(0);
x_111 = lean_box(0);
lean_inc(x_26);
x_112 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_26, x_109, x_110, x_26, x_26, x_111, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_108);
lean_dec(x_26);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_118 = x_112;
} else {
 lean_dec_ref(x_112);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_15, 0);
x_121 = lean_ctor_get(x_15, 1);
x_122 = lean_ctor_get(x_15, 2);
x_123 = lean_ctor_get(x_15, 3);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_15);
lean_inc(x_120);
x_124 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(x_120, x_1);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = lean_box(0);
lean_ctor_set(x_12, 0, x_125);
return x_12;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_free_object(x_12);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(x_120, x_1);
x_128 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_121);
lean_ctor_set(x_128, 2, x_122);
lean_ctor_set(x_128, 3, x_123);
x_129 = lean_st_ref_take(x_3, x_17);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 11);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_130, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_130, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_130, 6);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_130, sizeof(void*)*15);
x_141 = lean_ctor_get(x_130, 7);
lean_inc(x_141);
x_142 = lean_ctor_get(x_130, 8);
lean_inc(x_142);
x_143 = lean_ctor_get(x_130, 9);
lean_inc(x_143);
x_144 = lean_ctor_get(x_130, 10);
lean_inc(x_144);
x_145 = lean_ctor_get(x_130, 12);
lean_inc(x_145);
x_146 = lean_ctor_get(x_130, 13);
lean_inc(x_146);
x_147 = lean_ctor_get(x_130, 14);
lean_inc(x_147);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 lean_ctor_release(x_130, 6);
 lean_ctor_release(x_130, 7);
 lean_ctor_release(x_130, 8);
 lean_ctor_release(x_130, 9);
 lean_ctor_release(x_130, 10);
 lean_ctor_release(x_130, 11);
 lean_ctor_release(x_130, 12);
 lean_ctor_release(x_130, 13);
 lean_ctor_release(x_130, 14);
 x_148 = x_130;
} else {
 lean_dec_ref(x_130);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_131, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_131, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_131, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_131, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_131, 5);
lean_inc(x_153);
x_154 = lean_ctor_get(x_131, 6);
lean_inc(x_154);
x_155 = lean_ctor_get(x_131, 7);
lean_inc(x_155);
x_156 = lean_ctor_get(x_131, 8);
lean_inc(x_156);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 lean_ctor_release(x_131, 6);
 lean_ctor_release(x_131, 7);
 lean_ctor_release(x_131, 8);
 x_157 = x_131;
} else {
 lean_dec_ref(x_131);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 9, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_128);
lean_ctor_set(x_158, 1, x_149);
lean_ctor_set(x_158, 2, x_150);
lean_ctor_set(x_158, 3, x_151);
lean_ctor_set(x_158, 4, x_152);
lean_ctor_set(x_158, 5, x_153);
lean_ctor_set(x_158, 6, x_154);
lean_ctor_set(x_158, 7, x_155);
lean_ctor_set(x_158, 8, x_156);
if (lean_is_scalar(x_148)) {
 x_159 = lean_alloc_ctor(0, 15, 1);
} else {
 x_159 = x_148;
}
lean_ctor_set(x_159, 0, x_133);
lean_ctor_set(x_159, 1, x_134);
lean_ctor_set(x_159, 2, x_135);
lean_ctor_set(x_159, 3, x_136);
lean_ctor_set(x_159, 4, x_137);
lean_ctor_set(x_159, 5, x_138);
lean_ctor_set(x_159, 6, x_139);
lean_ctor_set(x_159, 7, x_141);
lean_ctor_set(x_159, 8, x_142);
lean_ctor_set(x_159, 9, x_143);
lean_ctor_set(x_159, 10, x_144);
lean_ctor_set(x_159, 11, x_158);
lean_ctor_set(x_159, 12, x_145);
lean_ctor_set(x_159, 13, x_146);
lean_ctor_set(x_159, 14, x_147);
lean_ctor_set_uint8(x_159, sizeof(void*)*15, x_140);
x_160 = lean_st_ref_set(x_3, x_159, x_132);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_st_ref_get(x_3, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 5);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_box(0);
x_167 = lean_box(0);
lean_inc(x_126);
x_168 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_126, x_165, x_166, x_126, x_126, x_167, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_126);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
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
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_12, 1);
lean_inc(x_176);
lean_dec(x_12);
x_177 = lean_ctor_get(x_15, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_15, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_15, 2);
lean_inc(x_179);
x_180 = lean_ctor_get(x_15, 3);
lean_inc(x_180);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 x_181 = x_15;
} else {
 lean_dec_ref(x_15);
 x_181 = lean_box(0);
}
lean_inc(x_177);
x_182 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(x_177, x_1);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_176);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
lean_dec(x_182);
x_186 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(x_177, x_1);
if (lean_is_scalar(x_181)) {
 x_187 = lean_alloc_ctor(0, 4, 0);
} else {
 x_187 = x_181;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_178);
lean_ctor_set(x_187, 2, x_179);
lean_ctor_set(x_187, 3, x_180);
x_188 = lean_st_ref_take(x_3, x_176);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 11);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_ctor_get(x_189, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 5);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 6);
lean_inc(x_198);
x_199 = lean_ctor_get_uint8(x_189, sizeof(void*)*15);
x_200 = lean_ctor_get(x_189, 7);
lean_inc(x_200);
x_201 = lean_ctor_get(x_189, 8);
lean_inc(x_201);
x_202 = lean_ctor_get(x_189, 9);
lean_inc(x_202);
x_203 = lean_ctor_get(x_189, 10);
lean_inc(x_203);
x_204 = lean_ctor_get(x_189, 12);
lean_inc(x_204);
x_205 = lean_ctor_get(x_189, 13);
lean_inc(x_205);
x_206 = lean_ctor_get(x_189, 14);
lean_inc(x_206);
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
 x_207 = x_189;
} else {
 lean_dec_ref(x_189);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_190, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_190, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_190, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_190, 4);
lean_inc(x_211);
x_212 = lean_ctor_get(x_190, 5);
lean_inc(x_212);
x_213 = lean_ctor_get(x_190, 6);
lean_inc(x_213);
x_214 = lean_ctor_get(x_190, 7);
lean_inc(x_214);
x_215 = lean_ctor_get(x_190, 8);
lean_inc(x_215);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 lean_ctor_release(x_190, 2);
 lean_ctor_release(x_190, 3);
 lean_ctor_release(x_190, 4);
 lean_ctor_release(x_190, 5);
 lean_ctor_release(x_190, 6);
 lean_ctor_release(x_190, 7);
 lean_ctor_release(x_190, 8);
 x_216 = x_190;
} else {
 lean_dec_ref(x_190);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 9, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_187);
lean_ctor_set(x_217, 1, x_208);
lean_ctor_set(x_217, 2, x_209);
lean_ctor_set(x_217, 3, x_210);
lean_ctor_set(x_217, 4, x_211);
lean_ctor_set(x_217, 5, x_212);
lean_ctor_set(x_217, 6, x_213);
lean_ctor_set(x_217, 7, x_214);
lean_ctor_set(x_217, 8, x_215);
if (lean_is_scalar(x_207)) {
 x_218 = lean_alloc_ctor(0, 15, 1);
} else {
 x_218 = x_207;
}
lean_ctor_set(x_218, 0, x_192);
lean_ctor_set(x_218, 1, x_193);
lean_ctor_set(x_218, 2, x_194);
lean_ctor_set(x_218, 3, x_195);
lean_ctor_set(x_218, 4, x_196);
lean_ctor_set(x_218, 5, x_197);
lean_ctor_set(x_218, 6, x_198);
lean_ctor_set(x_218, 7, x_200);
lean_ctor_set(x_218, 8, x_201);
lean_ctor_set(x_218, 9, x_202);
lean_ctor_set(x_218, 10, x_203);
lean_ctor_set(x_218, 11, x_217);
lean_ctor_set(x_218, 12, x_204);
lean_ctor_set(x_218, 13, x_205);
lean_ctor_set(x_218, 14, x_206);
lean_ctor_set_uint8(x_218, sizeof(void*)*15, x_199);
x_219 = lean_st_ref_set(x_3, x_218, x_191);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_st_ref_get(x_3, x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 5);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_box(0);
x_226 = lean_box(0);
lean_inc(x_185);
x_227 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_185, x_224, x_225, x_185, x_185, x_226, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_223);
lean_dec(x_185);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_227, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_233 = x_227;
} else {
 lean_dec_ref(x_227);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___boxed(lean_object** _args) {
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
x_18 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_Environment_find_x3f(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_11);
x_17 = 0;
x_18 = l_Lean_MessageData_ofConstName(x_1, x_17);
x_19 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__2(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = l_Lean_Environment_find_x3f(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = 0;
x_30 = l_Lean_MessageData_ofConstName(x_1, x_29);
x_31 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__2;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__2(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_whnfD(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Expr_getAppFn(x_17);
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_10, x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Environment_find_x3f(x_26, x_20);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_21);
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
x_28 = lean_box(0);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 5)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*6);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_21);
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
x_35 = lean_box(0);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_30, 4);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_21);
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
x_37 = lean_box(0);
lean_ctor_set(x_22, 0, x_37);
return x_22;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_22);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 6)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Expr_isAppOf(x_1, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 4);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_nat_dec_eq(x_49, x_33);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_30);
lean_dec(x_21);
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
x_51 = lean_box(0);
lean_ctor_set(x_40, 0, x_51);
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_40);
x_52 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_17, x_33);
x_53 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_52);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_17, x_54, x_56);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
lean_dec(x_30);
x_59 = l_Array_toSubarray___rarg(x_57, x_33, x_58);
x_60 = l_Lean_Expr_const___override(x_47, x_21);
x_61 = l_Array_ofSubarray___rarg(x_59);
lean_dec(x_59);
x_62 = l_Lean_mkAppN(x_60, x_61);
lean_dec(x_61);
x_63 = l_Lean_Meta_Grind_shareCommon(x_62, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_64);
x_67 = lean_grind_internalize(x_64, x_2, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_64);
x_69 = l_Lean_Meta_mkEqRefl(x_64, x_7, x_8, x_9, x_10, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = 0;
x_73 = l_Lean_Meta_Grind_pushEqCore(x_1, x_64, x_70, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_69);
if (x_74 == 0)
{
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
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
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
else
{
lean_object* x_82; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_30);
lean_dec(x_21);
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
x_82 = lean_box(0);
lean_ctor_set(x_40, 0, x_82);
return x_40;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_40, 1);
lean_inc(x_83);
lean_dec(x_40);
x_84 = lean_ctor_get(x_41, 0);
lean_inc(x_84);
lean_dec(x_41);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Expr_isAppOf(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 4);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_nat_dec_eq(x_88, x_33);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_86);
lean_dec(x_30);
lean_dec(x_21);
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
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_17, x_33);
x_93 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_92);
x_94 = lean_mk_array(x_92, x_93);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_sub(x_92, x_95);
lean_dec(x_92);
x_97 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_17, x_94, x_96);
x_98 = lean_ctor_get(x_30, 1);
lean_inc(x_98);
lean_dec(x_30);
x_99 = l_Array_toSubarray___rarg(x_97, x_33, x_98);
x_100 = l_Lean_Expr_const___override(x_86, x_21);
x_101 = l_Array_ofSubarray___rarg(x_99);
lean_dec(x_99);
x_102 = l_Lean_mkAppN(x_100, x_101);
lean_dec(x_101);
x_103 = l_Lean_Meta_Grind_shareCommon(x_102, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_83);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_104);
x_107 = lean_grind_internalize(x_104, x_2, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_104);
x_109 = l_Lean_Meta_mkEqRefl(x_104, x_7, x_8, x_9, x_10, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = 0;
x_113 = l_Lean_Meta_Grind_pushEqCore(x_1, x_104, x_110, x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_111);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_104);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = lean_ctor_get(x_107, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_107, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_120 = x_107;
} else {
 lean_dec_ref(x_107);
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
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_30);
lean_dec(x_21);
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
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_83);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_41);
lean_dec(x_30);
lean_dec(x_21);
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
x_124 = !lean_is_exclusive(x_40);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_40, 0);
lean_dec(x_125);
x_126 = lean_box(0);
lean_ctor_set(x_40, 0, x_126);
return x_40;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_40, 1);
lean_inc(x_127);
lean_dec(x_40);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_30);
lean_dec(x_21);
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
x_130 = !lean_is_exclusive(x_40);
if (x_130 == 0)
{
return x_40;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_40, 0);
x_132 = lean_ctor_get(x_40, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_40);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_21);
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
x_134 = lean_box(0);
lean_ctor_set(x_22, 0, x_134);
return x_22;
}
}
}
}
else
{
lean_object* x_135; 
lean_dec(x_30);
lean_dec(x_21);
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
x_135 = lean_box(0);
lean_ctor_set(x_22, 0, x_135);
return x_22;
}
}
else
{
lean_object* x_136; 
lean_dec(x_29);
lean_dec(x_21);
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
x_136 = lean_box(0);
lean_ctor_set(x_22, 0, x_136);
return x_22;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_22, 0);
x_138 = lean_ctor_get(x_22, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_22);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Environment_find_x3f(x_139, x_20);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_21);
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
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_138);
return x_142;
}
else
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
lean_dec(x_140);
if (lean_obj_tag(x_143) == 5)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_ctor_get_uint8(x_144, sizeof(void*)*6);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_144, 2);
lean_inc(x_146);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_nat_dec_eq(x_146, x_147);
lean_dec(x_146);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_144);
lean_dec(x_21);
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
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_138);
return x_150;
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_144, 4);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_144);
lean_dec(x_21);
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
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_138);
return x_153;
}
else
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
lean_dec(x_151);
x_156 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1(x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_138);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 6)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Expr_isAppOf(x_1, x_162);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_160, 4);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_nat_dec_eq(x_164, x_147);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_162);
lean_dec(x_144);
lean_dec(x_21);
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
x_166 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_159;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_158);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_159);
x_168 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_17, x_147);
x_169 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_168);
x_170 = lean_mk_array(x_168, x_169);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_sub(x_168, x_171);
lean_dec(x_168);
x_173 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_17, x_170, x_172);
x_174 = lean_ctor_get(x_144, 1);
lean_inc(x_174);
lean_dec(x_144);
x_175 = l_Array_toSubarray___rarg(x_173, x_147, x_174);
x_176 = l_Lean_Expr_const___override(x_162, x_21);
x_177 = l_Array_ofSubarray___rarg(x_175);
lean_dec(x_175);
x_178 = l_Lean_mkAppN(x_176, x_177);
lean_dec(x_177);
x_179 = l_Lean_Meta_Grind_shareCommon(x_178, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_158);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_180);
x_183 = lean_grind_internalize(x_180, x_2, x_182, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_181);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_180);
x_185 = l_Lean_Meta_mkEqRefl(x_180, x_7, x_8, x_9, x_10, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = 0;
x_189 = l_Lean_Meta_Grind_pushEqCore(x_1, x_180, x_186, x_188, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_187);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_180);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_190 = lean_ctor_get(x_185, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_192 = x_185;
} else {
 lean_dec_ref(x_185);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_180);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_194 = lean_ctor_get(x_183, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_183, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_196 = x_183;
} else {
 lean_dec_ref(x_183);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_144);
lean_dec(x_21);
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
x_198 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_159;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_158);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_157);
lean_dec(x_144);
lean_dec(x_21);
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
x_200 = lean_ctor_get(x_156, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_201 = x_156;
} else {
 lean_dec_ref(x_156);
 x_201 = lean_box(0);
}
x_202 = lean_box(0);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_200);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_144);
lean_dec(x_21);
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
x_204 = lean_ctor_get(x_156, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_156, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_206 = x_156;
} else {
 lean_dec_ref(x_156);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_154);
lean_dec(x_151);
lean_dec(x_144);
lean_dec(x_21);
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
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_138);
return x_209;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_144);
lean_dec(x_21);
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
x_210 = lean_box(0);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_138);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_143);
lean_dec(x_21);
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
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_138);
return x_213;
}
}
}
}
else
{
lean_object* x_214; 
lean_dec(x_19);
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
x_214 = lean_box(0);
lean_ctor_set(x_15, 0, x_214);
return x_15;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_15, 0);
x_216 = lean_ctor_get(x_15, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_15);
x_217 = l_Lean_Expr_getAppFn(x_215);
if (lean_obj_tag(x_217) == 4)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_st_ref_get(x_10, x_216);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
lean_dec(x_221);
x_225 = l_Lean_Environment_find_x3f(x_224, x_218);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_219);
lean_dec(x_215);
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
x_226 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_223;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_222);
return x_227;
}
else
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_225, 0);
lean_inc(x_228);
lean_dec(x_225);
if (lean_obj_tag(x_228) == 5)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get_uint8(x_229, sizeof(void*)*6);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_229, 2);
lean_inc(x_231);
x_232 = lean_unsigned_to_nat(0u);
x_233 = lean_nat_dec_eq(x_231, x_232);
lean_dec(x_231);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_234 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_223;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_222);
return x_235;
}
else
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_229, 4);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_237 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_223;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_222);
return x_238;
}
else
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_223);
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
lean_dec(x_236);
x_241 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1(x_240, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_222);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
if (lean_obj_tag(x_242) == 6)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec(x_246);
x_248 = l_Lean_Expr_isAppOf(x_1, x_247);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_245, 4);
lean_inc(x_249);
lean_dec(x_245);
x_250 = lean_nat_dec_eq(x_249, x_232);
lean_dec(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_247);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_251 = lean_box(0);
if (lean_is_scalar(x_244)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_244;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_243);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_244);
x_253 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_215, x_232);
x_254 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_253);
x_255 = lean_mk_array(x_253, x_254);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_sub(x_253, x_256);
lean_dec(x_253);
x_258 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_215, x_255, x_257);
x_259 = lean_ctor_get(x_229, 1);
lean_inc(x_259);
lean_dec(x_229);
x_260 = l_Array_toSubarray___rarg(x_258, x_232, x_259);
x_261 = l_Lean_Expr_const___override(x_247, x_219);
x_262 = l_Array_ofSubarray___rarg(x_260);
lean_dec(x_260);
x_263 = l_Lean_mkAppN(x_261, x_262);
lean_dec(x_262);
x_264 = l_Lean_Meta_Grind_shareCommon(x_263, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_243);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_265);
x_268 = lean_grind_internalize(x_265, x_2, x_267, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_265);
x_270 = l_Lean_Meta_mkEqRefl(x_265, x_7, x_8, x_9, x_10, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = 0;
x_274 = l_Lean_Meta_Grind_pushEqCore(x_1, x_265, x_271, x_273, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_272);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_265);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_275 = lean_ctor_get(x_270, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_270, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_277 = x_270;
} else {
 lean_dec_ref(x_270);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_265);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_279 = lean_ctor_get(x_268, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_268, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_281 = x_268;
} else {
 lean_dec_ref(x_268);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_283 = lean_box(0);
if (lean_is_scalar(x_244)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_244;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_243);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_242);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_285 = lean_ctor_get(x_241, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_286 = x_241;
} else {
 lean_dec_ref(x_241);
 x_286 = lean_box(0);
}
x_287 = lean_box(0);
if (lean_is_scalar(x_286)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_286;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_285);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_289 = lean_ctor_get(x_241, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_241, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_291 = x_241;
} else {
 lean_dec_ref(x_241);
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
lean_object* x_293; lean_object* x_294; 
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_293 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_223;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_222);
return x_294;
}
}
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_215);
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
x_295 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_223;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_222);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_228);
lean_dec(x_219);
lean_dec(x_215);
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
x_297 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_223;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_222);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_217);
lean_dec(x_215);
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
x_299 = lean_box(0);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_216);
return x_300;
}
}
}
else
{
uint8_t x_301; 
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
x_301 = !lean_is_exclusive(x_15);
if (x_301 == 0)
{
return x_15;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_15, 0);
x_303 = lean_ctor_get(x_15, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_15);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
else
{
uint8_t x_305; 
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
x_305 = !lean_is_exclusive(x_12);
if (x_305 == 0)
{
return x_12;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_12, 0);
x_307 = lean_ctor_get(x_12, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_12);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_nat_dec_lt(x_6, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_21 = lean_array_fget(x_3, x_6);
lean_inc(x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_21);
x_23 = lean_grind_internalize(x_21, x_2, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_1);
x_25 = l_Lean_Meta_Grind_registerParent(x_1, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_4, 2);
x_28 = lean_nat_add(x_6, x_27);
lean_dec(x_6);
x_29 = lean_box(0);
x_5 = x_29;
x_6 = x_28;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_17 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_Grind_mkENode(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_addCongrTable(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_20 = l_Lean_Meta_Grind_Arith_Offset_internalize(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_22 = l_Lean_Meta_Grind_propagateUp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_Grind_propagateBetaForNewApp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
return x_24;
}
else
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
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_registerParent(x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_get_size(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__1(x_1, x_4, x_3, x_21, x_22, x_19, lean_box(0), lean_box(0), x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_10(x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nestedProof", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_16; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_20 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_34; lean_object* x_69; uint8_t x_70; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
x_69 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_70 = l_Lean_Expr_isConstOf(x_4, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_34 = x_71;
goto block_68;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_array_get_size(x_5);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_nat_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_72);
x_75 = lean_box(0);
x_34 = x_75;
goto block_68;
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; 
lean_dec(x_22);
lean_dec(x_4);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_lt(x_76, x_72);
lean_dec(x_72);
lean_inc(x_1);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_1);
if (x_77 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_5);
x_79 = l_Lean_instInhabitedExpr;
x_80 = l_outOfBounds___rarg(x_79);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_80);
x_81 = lean_grind_internalize(x_80, x_2, x_78, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_1);
x_83 = l_Lean_Meta_Grind_registerParent(x_1, x_80, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_84, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_85);
lean_dec(x_84);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_80);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
return x_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_array_fget(x_5, x_76);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_91);
x_92 = lean_grind_internalize(x_91, x_2, x_78, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_1);
x_94 = l_Lean_Meta_Grind_registerParent(x_1, x_91, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_95, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_96);
lean_dec(x_95);
return x_97;
}
else
{
uint8_t x_98; 
lean_dec(x_91);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_92);
if (x_98 == 0)
{
return x_92;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_92, 0);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_92);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
block_33:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_23);
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_25 = lean_grind_internalize(x_4, x_2, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_22, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
lean_dec(x_26);
lean_dec(x_5);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_22);
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
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_68:
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_34);
x_35 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_36 = l_Lean_Expr_isConstOf(x_4, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_3);
x_37 = lean_box(0);
x_23 = x_37;
goto block_33;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_array_get_size(x_5);
x_39 = lean_unsigned_to_nat(5u);
x_40 = lean_nat_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_3);
x_41 = lean_box(0);
x_23 = x_41;
goto block_33;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_22);
lean_dec(x_4);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_lt(x_42, x_38);
lean_dec(x_38);
lean_inc(x_1);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_1);
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
x_45 = l_Lean_instInhabitedExpr;
x_46 = l_outOfBounds___rarg(x_45);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_46);
x_47 = lean_grind_internalize(x_46, x_2, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_1);
x_49 = l_Lean_Meta_Grind_registerParent(x_1, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_51);
lean_dec(x_50);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_46);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_array_fget(x_5, x_42);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_57);
x_58 = lean_grind_internalize(x_57, x_2, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_1);
x_60 = l_Lean_Meta_Grind_registerParent(x_1, x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_62);
lean_dec(x_61);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_57);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_58);
if (x_64 == 0)
{
return x_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
}
else
{
uint8_t x_102; 
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
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_20);
if (x_102 == 0)
{
return x_20;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_20, 0);
x_104 = lean_ctor_get(x_20, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_20);
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
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_16);
if (x_106 == 0)
{
return x_16;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_16, 0);
x_108 = lean_ctor_get(x_16, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_16);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
case 1:
{
lean_object* x_110; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_110 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
lean_inc(x_1);
x_112 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_111);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_114 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_128; lean_object* x_163; uint8_t x_164; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_116 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_116, 0, x_1);
lean_closure_set(x_116, 1, x_2);
lean_closure_set(x_116, 2, x_3);
x_163 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_164 = l_Lean_Expr_isConstOf(x_4, x_163);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_box(0);
x_128 = x_165;
goto block_162;
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_array_get_size(x_5);
x_167 = lean_unsigned_to_nat(2u);
x_168 = lean_nat_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_166);
x_169 = lean_box(0);
x_128 = x_169;
goto block_162;
}
else
{
lean_object* x_170; uint8_t x_171; lean_object* x_172; 
lean_dec(x_116);
lean_dec(x_4);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_nat_dec_lt(x_170, x_166);
lean_dec(x_166);
lean_inc(x_1);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_1);
if (x_171 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_5);
x_173 = l_Lean_instInhabitedExpr;
x_174 = l_outOfBounds___rarg(x_173);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_174);
x_175 = lean_grind_internalize(x_174, x_2, x_172, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
lean_inc(x_1);
x_177 = l_Lean_Meta_Grind_registerParent(x_1, x_174, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_178, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_179);
lean_dec(x_178);
return x_180;
}
else
{
uint8_t x_181; 
lean_dec(x_174);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_175);
if (x_181 == 0)
{
return x_175;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_175, 0);
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_175);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_array_fget(x_5, x_170);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_185);
x_186 = lean_grind_internalize(x_185, x_2, x_172, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
lean_inc(x_1);
x_188 = l_Lean_Meta_Grind_registerParent(x_1, x_185, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_189, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_190);
lean_dec(x_189);
return x_191;
}
else
{
uint8_t x_192; 
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_186);
if (x_192 == 0)
{
return x_186;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_186, 0);
x_194 = lean_ctor_get(x_186, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_186);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
}
block_127:
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_117);
lean_inc(x_1);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_119 = lean_grind_internalize(x_4, x_2, x_118, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_116, x_120, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_121);
lean_dec(x_120);
lean_dec(x_5);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_116);
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
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_119);
if (x_123 == 0)
{
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_119, 0);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_119);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
block_162:
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_128);
x_129 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_130 = l_Lean_Expr_isConstOf(x_4, x_129);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_3);
x_131 = lean_box(0);
x_117 = x_131;
goto block_127;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_array_get_size(x_5);
x_133 = lean_unsigned_to_nat(5u);
x_134 = lean_nat_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_3);
x_135 = lean_box(0);
x_117 = x_135;
goto block_127;
}
else
{
lean_object* x_136; uint8_t x_137; lean_object* x_138; 
lean_dec(x_116);
lean_dec(x_4);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_dec_lt(x_136, x_132);
lean_dec(x_132);
lean_inc(x_1);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_1);
if (x_137 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_5);
x_139 = l_Lean_instInhabitedExpr;
x_140 = l_outOfBounds___rarg(x_139);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_140);
x_141 = lean_grind_internalize(x_140, x_2, x_138, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
lean_inc(x_1);
x_143 = l_Lean_Meta_Grind_registerParent(x_1, x_140, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_144, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_145);
lean_dec(x_144);
return x_146;
}
else
{
uint8_t x_147; 
lean_dec(x_140);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_141);
if (x_147 == 0)
{
return x_141;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_141, 0);
x_149 = lean_ctor_get(x_141, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_141);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_array_fget(x_5, x_136);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_151);
x_152 = lean_grind_internalize(x_151, x_2, x_138, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
lean_inc(x_1);
x_154 = l_Lean_Meta_Grind_registerParent(x_1, x_151, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_155, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_156);
lean_dec(x_155);
return x_157;
}
else
{
uint8_t x_158; 
lean_dec(x_151);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_152);
if (x_158 == 0)
{
return x_152;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_152, 0);
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_152);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
}
}
}
else
{
uint8_t x_196; 
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
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_114);
if (x_196 == 0)
{
return x_114;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_114, 0);
x_198 = lean_ctor_get(x_114, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_114);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; 
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
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_110);
if (x_200 == 0)
{
return x_110;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_110, 0);
x_202 = lean_ctor_get(x_110, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_110);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
case 2:
{
lean_object* x_204; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_204 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
lean_inc(x_1);
x_206 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_205);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_208 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_222; lean_object* x_257; uint8_t x_258; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_210 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_210, 0, x_1);
lean_closure_set(x_210, 1, x_2);
lean_closure_set(x_210, 2, x_3);
x_257 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_258 = l_Lean_Expr_isConstOf(x_4, x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_box(0);
x_222 = x_259;
goto block_256;
}
else
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_260 = lean_array_get_size(x_5);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_nat_dec_eq(x_260, x_261);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_260);
x_263 = lean_box(0);
x_222 = x_263;
goto block_256;
}
else
{
lean_object* x_264; uint8_t x_265; lean_object* x_266; 
lean_dec(x_210);
lean_dec(x_4);
x_264 = lean_unsigned_to_nat(0u);
x_265 = lean_nat_dec_lt(x_264, x_260);
lean_dec(x_260);
lean_inc(x_1);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_1);
if (x_265 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_5);
x_267 = l_Lean_instInhabitedExpr;
x_268 = l_outOfBounds___rarg(x_267);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_268);
x_269 = lean_grind_internalize(x_268, x_2, x_266, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_209);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
lean_inc(x_1);
x_271 = l_Lean_Meta_Grind_registerParent(x_1, x_268, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_272, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_273);
lean_dec(x_272);
return x_274;
}
else
{
uint8_t x_275; 
lean_dec(x_268);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_269);
if (x_275 == 0)
{
return x_269;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_269, 0);
x_277 = lean_ctor_get(x_269, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_269);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_array_fget(x_5, x_264);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_279);
x_280 = lean_grind_internalize(x_279, x_2, x_266, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_209);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
lean_inc(x_1);
x_282 = l_Lean_Meta_Grind_registerParent(x_1, x_279, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_281);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_283, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_284);
lean_dec(x_283);
return x_285;
}
else
{
uint8_t x_286; 
lean_dec(x_279);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = !lean_is_exclusive(x_280);
if (x_286 == 0)
{
return x_280;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_280, 0);
x_288 = lean_ctor_get(x_280, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_280);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
}
}
block_221:
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_211);
lean_inc(x_1);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_213 = lean_grind_internalize(x_4, x_2, x_212, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_209);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_210, x_214, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_215);
lean_dec(x_214);
lean_dec(x_5);
return x_216;
}
else
{
uint8_t x_217; 
lean_dec(x_210);
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
lean_dec(x_2);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_213);
if (x_217 == 0)
{
return x_213;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_213, 0);
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_213);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
block_256:
{
lean_object* x_223; uint8_t x_224; 
lean_dec(x_222);
x_223 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_224 = l_Lean_Expr_isConstOf(x_4, x_223);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_3);
x_225 = lean_box(0);
x_211 = x_225;
goto block_221;
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_array_get_size(x_5);
x_227 = lean_unsigned_to_nat(5u);
x_228 = lean_nat_dec_eq(x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_226);
lean_dec(x_3);
x_229 = lean_box(0);
x_211 = x_229;
goto block_221;
}
else
{
lean_object* x_230; uint8_t x_231; lean_object* x_232; 
lean_dec(x_210);
lean_dec(x_4);
x_230 = lean_unsigned_to_nat(1u);
x_231 = lean_nat_dec_lt(x_230, x_226);
lean_dec(x_226);
lean_inc(x_1);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_1);
if (x_231 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_5);
x_233 = l_Lean_instInhabitedExpr;
x_234 = l_outOfBounds___rarg(x_233);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_234);
x_235 = lean_grind_internalize(x_234, x_2, x_232, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_209);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
lean_inc(x_1);
x_237 = l_Lean_Meta_Grind_registerParent(x_1, x_234, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_238, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_239);
lean_dec(x_238);
return x_240;
}
else
{
uint8_t x_241; 
lean_dec(x_234);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_235);
if (x_241 == 0)
{
return x_235;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_235, 0);
x_243 = lean_ctor_get(x_235, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_235);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_array_fget(x_5, x_230);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_245);
x_246 = lean_grind_internalize(x_245, x_2, x_232, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_209);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
lean_inc(x_1);
x_248 = l_Lean_Meta_Grind_registerParent(x_1, x_245, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_249, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_250);
lean_dec(x_249);
return x_251;
}
else
{
uint8_t x_252; 
lean_dec(x_245);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_246);
if (x_252 == 0)
{
return x_246;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_246, 0);
x_254 = lean_ctor_get(x_246, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_246);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
}
}
}
}
else
{
uint8_t x_290; 
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
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_208);
if (x_290 == 0)
{
return x_208;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_208, 0);
x_292 = lean_ctor_get(x_208, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_208);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
uint8_t x_294; 
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
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_204);
if (x_294 == 0)
{
return x_204;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_204, 0);
x_296 = lean_ctor_get(x_204, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_204);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
case 3:
{
lean_object* x_298; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_298 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
lean_inc(x_1);
x_300 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_299);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec(x_300);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_302 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_316; lean_object* x_351; uint8_t x_352; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_304 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_304, 0, x_1);
lean_closure_set(x_304, 1, x_2);
lean_closure_set(x_304, 2, x_3);
x_351 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_352 = l_Lean_Expr_isConstOf(x_4, x_351);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_box(0);
x_316 = x_353;
goto block_350;
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_354 = lean_array_get_size(x_5);
x_355 = lean_unsigned_to_nat(2u);
x_356 = lean_nat_dec_eq(x_354, x_355);
if (x_356 == 0)
{
lean_object* x_357; 
lean_dec(x_354);
x_357 = lean_box(0);
x_316 = x_357;
goto block_350;
}
else
{
lean_object* x_358; uint8_t x_359; lean_object* x_360; 
lean_dec(x_304);
lean_dec(x_4);
x_358 = lean_unsigned_to_nat(0u);
x_359 = lean_nat_dec_lt(x_358, x_354);
lean_dec(x_354);
lean_inc(x_1);
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_1);
if (x_359 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_5);
x_361 = l_Lean_instInhabitedExpr;
x_362 = l_outOfBounds___rarg(x_361);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_362);
x_363 = lean_grind_internalize(x_362, x_2, x_360, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_303);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
lean_inc(x_1);
x_365 = l_Lean_Meta_Grind_registerParent(x_1, x_362, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_364);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_366, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_367);
lean_dec(x_366);
return x_368;
}
else
{
uint8_t x_369; 
lean_dec(x_362);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_369 = !lean_is_exclusive(x_363);
if (x_369 == 0)
{
return x_363;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_363, 0);
x_371 = lean_ctor_get(x_363, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_363);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_array_fget(x_5, x_358);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_373);
x_374 = lean_grind_internalize(x_373, x_2, x_360, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_303);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
lean_dec(x_374);
lean_inc(x_1);
x_376 = l_Lean_Meta_Grind_registerParent(x_1, x_373, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_377, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_378);
lean_dec(x_377);
return x_379;
}
else
{
uint8_t x_380; 
lean_dec(x_373);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_380 = !lean_is_exclusive(x_374);
if (x_380 == 0)
{
return x_374;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_374, 0);
x_382 = lean_ctor_get(x_374, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_374);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
}
}
block_315:
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_305);
lean_inc(x_1);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_307 = lean_grind_internalize(x_4, x_2, x_306, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_303);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_304, x_308, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_309);
lean_dec(x_308);
lean_dec(x_5);
return x_310;
}
else
{
uint8_t x_311; 
lean_dec(x_304);
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
lean_dec(x_2);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_307);
if (x_311 == 0)
{
return x_307;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_307, 0);
x_313 = lean_ctor_get(x_307, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_307);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
block_350:
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_316);
x_317 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_318 = l_Lean_Expr_isConstOf(x_4, x_317);
if (x_318 == 0)
{
lean_object* x_319; 
lean_dec(x_3);
x_319 = lean_box(0);
x_305 = x_319;
goto block_315;
}
else
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_320 = lean_array_get_size(x_5);
x_321 = lean_unsigned_to_nat(5u);
x_322 = lean_nat_dec_eq(x_320, x_321);
if (x_322 == 0)
{
lean_object* x_323; 
lean_dec(x_320);
lean_dec(x_3);
x_323 = lean_box(0);
x_305 = x_323;
goto block_315;
}
else
{
lean_object* x_324; uint8_t x_325; lean_object* x_326; 
lean_dec(x_304);
lean_dec(x_4);
x_324 = lean_unsigned_to_nat(1u);
x_325 = lean_nat_dec_lt(x_324, x_320);
lean_dec(x_320);
lean_inc(x_1);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_1);
if (x_325 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_5);
x_327 = l_Lean_instInhabitedExpr;
x_328 = l_outOfBounds___rarg(x_327);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_328);
x_329 = lean_grind_internalize(x_328, x_2, x_326, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_303);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
lean_inc(x_1);
x_331 = l_Lean_Meta_Grind_registerParent(x_1, x_328, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_330);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_332, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_333);
lean_dec(x_332);
return x_334;
}
else
{
uint8_t x_335; 
lean_dec(x_328);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_329);
if (x_335 == 0)
{
return x_329;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_329, 0);
x_337 = lean_ctor_get(x_329, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_329);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_array_fget(x_5, x_324);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_339);
x_340 = lean_grind_internalize(x_339, x_2, x_326, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_303);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
lean_inc(x_1);
x_342 = l_Lean_Meta_Grind_registerParent(x_1, x_339, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_341);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_343, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_344);
lean_dec(x_343);
return x_345;
}
else
{
uint8_t x_346; 
lean_dec(x_339);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_346 = !lean_is_exclusive(x_340);
if (x_346 == 0)
{
return x_340;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_340, 0);
x_348 = lean_ctor_get(x_340, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_340);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
}
}
}
}
else
{
uint8_t x_384; 
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
lean_dec(x_1);
x_384 = !lean_is_exclusive(x_302);
if (x_384 == 0)
{
return x_302;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_302, 0);
x_386 = lean_ctor_get(x_302, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_302);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
else
{
uint8_t x_388; 
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
lean_dec(x_1);
x_388 = !lean_is_exclusive(x_298);
if (x_388 == 0)
{
return x_298;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_298, 0);
x_390 = lean_ctor_get(x_298, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_298);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
}
case 4:
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_6);
x_392 = lean_ctor_get(x_4, 0);
lean_inc(x_392);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_393 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
lean_inc(x_1);
x_395 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_394);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_397 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_396);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_410; lean_object* x_445; uint8_t x_446; 
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_399 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_399, 0, x_1);
lean_closure_set(x_399, 1, x_2);
lean_closure_set(x_399, 2, x_3);
x_445 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_446 = l_Lean_Expr_isConstOf(x_4, x_445);
if (x_446 == 0)
{
lean_object* x_447; 
x_447 = lean_box(0);
x_410 = x_447;
goto block_444;
}
else
{
lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_448 = lean_array_get_size(x_5);
x_449 = lean_unsigned_to_nat(2u);
x_450 = lean_nat_dec_eq(x_448, x_449);
if (x_450 == 0)
{
lean_object* x_451; 
lean_dec(x_448);
x_451 = lean_box(0);
x_410 = x_451;
goto block_444;
}
else
{
lean_object* x_452; uint8_t x_453; lean_object* x_454; 
lean_dec(x_399);
lean_dec(x_392);
lean_dec(x_4);
x_452 = lean_unsigned_to_nat(0u);
x_453 = lean_nat_dec_lt(x_452, x_448);
lean_dec(x_448);
lean_inc(x_1);
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_1);
if (x_453 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_5);
x_455 = l_Lean_instInhabitedExpr;
x_456 = l_outOfBounds___rarg(x_455);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_456);
x_457 = lean_grind_internalize(x_456, x_2, x_454, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_398);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
lean_dec(x_457);
lean_inc(x_1);
x_459 = l_Lean_Meta_Grind_registerParent(x_1, x_456, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_458);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_460, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_461);
lean_dec(x_460);
return x_462;
}
else
{
uint8_t x_463; 
lean_dec(x_456);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_463 = !lean_is_exclusive(x_457);
if (x_463 == 0)
{
return x_457;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_457, 0);
x_465 = lean_ctor_get(x_457, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_457);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
else
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_array_fget(x_5, x_452);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_467);
x_468 = lean_grind_internalize(x_467, x_2, x_454, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_398);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
lean_inc(x_1);
x_470 = l_Lean_Meta_Grind_registerParent(x_1, x_467, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_469);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_471, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_472);
lean_dec(x_471);
return x_473;
}
else
{
uint8_t x_474; 
lean_dec(x_467);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_474 = !lean_is_exclusive(x_468);
if (x_474 == 0)
{
return x_468;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_468, 0);
x_476 = lean_ctor_get(x_468, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_468);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
}
}
block_409:
{
lean_object* x_401; 
lean_dec(x_400);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_401 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(x_392, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_398);
lean_dec(x_392);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_399, x_402, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_403);
lean_dec(x_402);
lean_dec(x_5);
return x_404;
}
else
{
uint8_t x_405; 
lean_dec(x_399);
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
lean_dec(x_2);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_401);
if (x_405 == 0)
{
return x_401;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_401, 0);
x_407 = lean_ctor_get(x_401, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_401);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
block_444:
{
lean_object* x_411; uint8_t x_412; 
lean_dec(x_410);
x_411 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_412 = l_Lean_Expr_isConstOf(x_4, x_411);
if (x_412 == 0)
{
lean_object* x_413; 
lean_dec(x_3);
x_413 = lean_box(0);
x_400 = x_413;
goto block_409;
}
else
{
lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_414 = lean_array_get_size(x_5);
x_415 = lean_unsigned_to_nat(5u);
x_416 = lean_nat_dec_eq(x_414, x_415);
if (x_416 == 0)
{
lean_object* x_417; 
lean_dec(x_414);
lean_dec(x_3);
x_417 = lean_box(0);
x_400 = x_417;
goto block_409;
}
else
{
lean_object* x_418; uint8_t x_419; lean_object* x_420; 
lean_dec(x_399);
lean_dec(x_392);
lean_dec(x_4);
x_418 = lean_unsigned_to_nat(1u);
x_419 = lean_nat_dec_lt(x_418, x_414);
lean_dec(x_414);
lean_inc(x_1);
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_1);
if (x_419 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_5);
x_421 = l_Lean_instInhabitedExpr;
x_422 = l_outOfBounds___rarg(x_421);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_422);
x_423 = lean_grind_internalize(x_422, x_2, x_420, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_398);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
lean_inc(x_1);
x_425 = l_Lean_Meta_Grind_registerParent(x_1, x_422, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_424);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_426, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_427);
lean_dec(x_426);
return x_428;
}
else
{
uint8_t x_429; 
lean_dec(x_422);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_429 = !lean_is_exclusive(x_423);
if (x_429 == 0)
{
return x_423;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_423, 0);
x_431 = lean_ctor_get(x_423, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_423);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_array_fget(x_5, x_418);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_433);
x_434 = lean_grind_internalize(x_433, x_2, x_420, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_398);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
lean_inc(x_1);
x_436 = l_Lean_Meta_Grind_registerParent(x_1, x_433, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_435);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_437, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_438);
lean_dec(x_437);
return x_439;
}
else
{
uint8_t x_440; 
lean_dec(x_433);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_434);
if (x_440 == 0)
{
return x_434;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_434, 0);
x_442 = lean_ctor_get(x_434, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_434);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
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
uint8_t x_478; 
lean_dec(x_392);
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
lean_dec(x_1);
x_478 = !lean_is_exclusive(x_397);
if (x_478 == 0)
{
return x_397;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_397, 0);
x_480 = lean_ctor_get(x_397, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_397);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_392);
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
lean_dec(x_1);
x_482 = !lean_is_exclusive(x_393);
if (x_482 == 0)
{
return x_393;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_393, 0);
x_484 = lean_ctor_get(x_393, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_393);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
case 5:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_486 = lean_ctor_get(x_4, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_4, 1);
lean_inc(x_487);
lean_dec(x_4);
x_488 = lean_array_set(x_5, x_6, x_487);
x_489 = lean_unsigned_to_nat(1u);
x_490 = lean_nat_sub(x_6, x_489);
lean_dec(x_6);
x_4 = x_486;
x_5 = x_488;
x_6 = x_490;
goto _start;
}
case 6:
{
lean_object* x_492; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_492 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
lean_inc(x_1);
x_494 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_493);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec(x_494);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_496 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_510; lean_object* x_545; uint8_t x_546; 
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_498 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_498, 0, x_1);
lean_closure_set(x_498, 1, x_2);
lean_closure_set(x_498, 2, x_3);
x_545 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_546 = l_Lean_Expr_isConstOf(x_4, x_545);
if (x_546 == 0)
{
lean_object* x_547; 
x_547 = lean_box(0);
x_510 = x_547;
goto block_544;
}
else
{
lean_object* x_548; lean_object* x_549; uint8_t x_550; 
x_548 = lean_array_get_size(x_5);
x_549 = lean_unsigned_to_nat(2u);
x_550 = lean_nat_dec_eq(x_548, x_549);
if (x_550 == 0)
{
lean_object* x_551; 
lean_dec(x_548);
x_551 = lean_box(0);
x_510 = x_551;
goto block_544;
}
else
{
lean_object* x_552; uint8_t x_553; lean_object* x_554; 
lean_dec(x_498);
lean_dec(x_4);
x_552 = lean_unsigned_to_nat(0u);
x_553 = lean_nat_dec_lt(x_552, x_548);
lean_dec(x_548);
lean_inc(x_1);
x_554 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_554, 0, x_1);
if (x_553 == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_5);
x_555 = l_Lean_instInhabitedExpr;
x_556 = l_outOfBounds___rarg(x_555);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_556);
x_557 = lean_grind_internalize(x_556, x_2, x_554, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_497);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_558 = lean_ctor_get(x_557, 1);
lean_inc(x_558);
lean_dec(x_557);
lean_inc(x_1);
x_559 = l_Lean_Meta_Grind_registerParent(x_1, x_556, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_558);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_560, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_561);
lean_dec(x_560);
return x_562;
}
else
{
uint8_t x_563; 
lean_dec(x_556);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_557);
if (x_563 == 0)
{
return x_557;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_557, 0);
x_565 = lean_ctor_get(x_557, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_557);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
else
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_array_fget(x_5, x_552);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_567);
x_568 = lean_grind_internalize(x_567, x_2, x_554, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_497);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_569 = lean_ctor_get(x_568, 1);
lean_inc(x_569);
lean_dec(x_568);
lean_inc(x_1);
x_570 = l_Lean_Meta_Grind_registerParent(x_1, x_567, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_569);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
x_573 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_571, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_572);
lean_dec(x_571);
return x_573;
}
else
{
uint8_t x_574; 
lean_dec(x_567);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_574 = !lean_is_exclusive(x_568);
if (x_574 == 0)
{
return x_568;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_568, 0);
x_576 = lean_ctor_get(x_568, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_568);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set(x_577, 1, x_576);
return x_577;
}
}
}
}
}
block_509:
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_499);
lean_inc(x_1);
x_500 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_500, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_501 = lean_grind_internalize(x_4, x_2, x_500, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_497);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_504 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_498, x_502, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_503);
lean_dec(x_502);
lean_dec(x_5);
return x_504;
}
else
{
uint8_t x_505; 
lean_dec(x_498);
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
lean_dec(x_2);
lean_dec(x_1);
x_505 = !lean_is_exclusive(x_501);
if (x_505 == 0)
{
return x_501;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_501, 0);
x_507 = lean_ctor_get(x_501, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_501);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
block_544:
{
lean_object* x_511; uint8_t x_512; 
lean_dec(x_510);
x_511 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_512 = l_Lean_Expr_isConstOf(x_4, x_511);
if (x_512 == 0)
{
lean_object* x_513; 
lean_dec(x_3);
x_513 = lean_box(0);
x_499 = x_513;
goto block_509;
}
else
{
lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_514 = lean_array_get_size(x_5);
x_515 = lean_unsigned_to_nat(5u);
x_516 = lean_nat_dec_eq(x_514, x_515);
if (x_516 == 0)
{
lean_object* x_517; 
lean_dec(x_514);
lean_dec(x_3);
x_517 = lean_box(0);
x_499 = x_517;
goto block_509;
}
else
{
lean_object* x_518; uint8_t x_519; lean_object* x_520; 
lean_dec(x_498);
lean_dec(x_4);
x_518 = lean_unsigned_to_nat(1u);
x_519 = lean_nat_dec_lt(x_518, x_514);
lean_dec(x_514);
lean_inc(x_1);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_1);
if (x_519 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_5);
x_521 = l_Lean_instInhabitedExpr;
x_522 = l_outOfBounds___rarg(x_521);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_522);
x_523 = lean_grind_internalize(x_522, x_2, x_520, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_497);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
lean_dec(x_523);
lean_inc(x_1);
x_525 = l_Lean_Meta_Grind_registerParent(x_1, x_522, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_524);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_526, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_527);
lean_dec(x_526);
return x_528;
}
else
{
uint8_t x_529; 
lean_dec(x_522);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_529 = !lean_is_exclusive(x_523);
if (x_529 == 0)
{
return x_523;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_523, 0);
x_531 = lean_ctor_get(x_523, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_523);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
else
{
lean_object* x_533; lean_object* x_534; 
x_533 = lean_array_fget(x_5, x_518);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_533);
x_534 = lean_grind_internalize(x_533, x_2, x_520, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_497);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
lean_inc(x_1);
x_536 = l_Lean_Meta_Grind_registerParent(x_1, x_533, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_535);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_537, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_538);
lean_dec(x_537);
return x_539;
}
else
{
uint8_t x_540; 
lean_dec(x_533);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_540 = !lean_is_exclusive(x_534);
if (x_540 == 0)
{
return x_534;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_534, 0);
x_542 = lean_ctor_get(x_534, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_534);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
}
}
}
}
else
{
uint8_t x_578; 
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
lean_dec(x_1);
x_578 = !lean_is_exclusive(x_496);
if (x_578 == 0)
{
return x_496;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_496, 0);
x_580 = lean_ctor_get(x_496, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_496);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
return x_581;
}
}
}
else
{
uint8_t x_582; 
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
lean_dec(x_1);
x_582 = !lean_is_exclusive(x_492);
if (x_582 == 0)
{
return x_492;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_492, 0);
x_584 = lean_ctor_get(x_492, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_492);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
case 7:
{
lean_object* x_586; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_586 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
lean_inc(x_1);
x_588 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_587);
x_589 = lean_ctor_get(x_588, 1);
lean_inc(x_589);
lean_dec(x_588);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_590 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_589);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_604; lean_object* x_639; uint8_t x_640; 
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
lean_dec(x_590);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_592 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_592, 0, x_1);
lean_closure_set(x_592, 1, x_2);
lean_closure_set(x_592, 2, x_3);
x_639 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_640 = l_Lean_Expr_isConstOf(x_4, x_639);
if (x_640 == 0)
{
lean_object* x_641; 
x_641 = lean_box(0);
x_604 = x_641;
goto block_638;
}
else
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; 
x_642 = lean_array_get_size(x_5);
x_643 = lean_unsigned_to_nat(2u);
x_644 = lean_nat_dec_eq(x_642, x_643);
if (x_644 == 0)
{
lean_object* x_645; 
lean_dec(x_642);
x_645 = lean_box(0);
x_604 = x_645;
goto block_638;
}
else
{
lean_object* x_646; uint8_t x_647; lean_object* x_648; 
lean_dec(x_592);
lean_dec(x_4);
x_646 = lean_unsigned_to_nat(0u);
x_647 = lean_nat_dec_lt(x_646, x_642);
lean_dec(x_642);
lean_inc(x_1);
x_648 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_648, 0, x_1);
if (x_647 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_5);
x_649 = l_Lean_instInhabitedExpr;
x_650 = l_outOfBounds___rarg(x_649);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_650);
x_651 = lean_grind_internalize(x_650, x_2, x_648, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_591);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_652 = lean_ctor_get(x_651, 1);
lean_inc(x_652);
lean_dec(x_651);
lean_inc(x_1);
x_653 = l_Lean_Meta_Grind_registerParent(x_1, x_650, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_652);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_654, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_655);
lean_dec(x_654);
return x_656;
}
else
{
uint8_t x_657; 
lean_dec(x_650);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_657 = !lean_is_exclusive(x_651);
if (x_657 == 0)
{
return x_651;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_651, 0);
x_659 = lean_ctor_get(x_651, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_651);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_array_fget(x_5, x_646);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_661);
x_662 = lean_grind_internalize(x_661, x_2, x_648, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_591);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_663 = lean_ctor_get(x_662, 1);
lean_inc(x_663);
lean_dec(x_662);
lean_inc(x_1);
x_664 = l_Lean_Meta_Grind_registerParent(x_1, x_661, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_663);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_665, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_666);
lean_dec(x_665);
return x_667;
}
else
{
uint8_t x_668; 
lean_dec(x_661);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_668 = !lean_is_exclusive(x_662);
if (x_668 == 0)
{
return x_662;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_662, 0);
x_670 = lean_ctor_get(x_662, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_662);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
return x_671;
}
}
}
}
}
block_603:
{
lean_object* x_594; lean_object* x_595; 
lean_dec(x_593);
lean_inc(x_1);
x_594 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_594, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_595 = lean_grind_internalize(x_4, x_2, x_594, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_591);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_592, x_596, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_597);
lean_dec(x_596);
lean_dec(x_5);
return x_598;
}
else
{
uint8_t x_599; 
lean_dec(x_592);
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
lean_dec(x_2);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_595);
if (x_599 == 0)
{
return x_595;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_595, 0);
x_601 = lean_ctor_get(x_595, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_595);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
block_638:
{
lean_object* x_605; uint8_t x_606; 
lean_dec(x_604);
x_605 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_606 = l_Lean_Expr_isConstOf(x_4, x_605);
if (x_606 == 0)
{
lean_object* x_607; 
lean_dec(x_3);
x_607 = lean_box(0);
x_593 = x_607;
goto block_603;
}
else
{
lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_608 = lean_array_get_size(x_5);
x_609 = lean_unsigned_to_nat(5u);
x_610 = lean_nat_dec_eq(x_608, x_609);
if (x_610 == 0)
{
lean_object* x_611; 
lean_dec(x_608);
lean_dec(x_3);
x_611 = lean_box(0);
x_593 = x_611;
goto block_603;
}
else
{
lean_object* x_612; uint8_t x_613; lean_object* x_614; 
lean_dec(x_592);
lean_dec(x_4);
x_612 = lean_unsigned_to_nat(1u);
x_613 = lean_nat_dec_lt(x_612, x_608);
lean_dec(x_608);
lean_inc(x_1);
x_614 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_614, 0, x_1);
if (x_613 == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_5);
x_615 = l_Lean_instInhabitedExpr;
x_616 = l_outOfBounds___rarg(x_615);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_616);
x_617 = lean_grind_internalize(x_616, x_2, x_614, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_591);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
lean_inc(x_1);
x_619 = l_Lean_Meta_Grind_registerParent(x_1, x_616, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_618);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_620, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_621);
lean_dec(x_620);
return x_622;
}
else
{
uint8_t x_623; 
lean_dec(x_616);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_623 = !lean_is_exclusive(x_617);
if (x_623 == 0)
{
return x_617;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_617, 0);
x_625 = lean_ctor_get(x_617, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_617);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_625);
return x_626;
}
}
}
else
{
lean_object* x_627; lean_object* x_628; 
x_627 = lean_array_fget(x_5, x_612);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_627);
x_628 = lean_grind_internalize(x_627, x_2, x_614, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_591);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_628, 1);
lean_inc(x_629);
lean_dec(x_628);
lean_inc(x_1);
x_630 = l_Lean_Meta_Grind_registerParent(x_1, x_627, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_629);
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_630, 1);
lean_inc(x_632);
lean_dec(x_630);
x_633 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_631, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_632);
lean_dec(x_631);
return x_633;
}
else
{
uint8_t x_634; 
lean_dec(x_627);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_634 = !lean_is_exclusive(x_628);
if (x_634 == 0)
{
return x_628;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_628, 0);
x_636 = lean_ctor_get(x_628, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_628);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
}
}
}
}
else
{
uint8_t x_672; 
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
lean_dec(x_1);
x_672 = !lean_is_exclusive(x_590);
if (x_672 == 0)
{
return x_590;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_590, 0);
x_674 = lean_ctor_get(x_590, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_590);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
else
{
uint8_t x_676; 
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
lean_dec(x_1);
x_676 = !lean_is_exclusive(x_586);
if (x_676 == 0)
{
return x_586;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_586, 0);
x_678 = lean_ctor_get(x_586, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_586);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
}
case 8:
{
lean_object* x_680; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_680 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
lean_dec(x_680);
lean_inc(x_1);
x_682 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_681);
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
lean_dec(x_682);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_684 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_683);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_698; lean_object* x_733; uint8_t x_734; 
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec(x_684);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_686 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_686, 0, x_1);
lean_closure_set(x_686, 1, x_2);
lean_closure_set(x_686, 2, x_3);
x_733 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_734 = l_Lean_Expr_isConstOf(x_4, x_733);
if (x_734 == 0)
{
lean_object* x_735; 
x_735 = lean_box(0);
x_698 = x_735;
goto block_732;
}
else
{
lean_object* x_736; lean_object* x_737; uint8_t x_738; 
x_736 = lean_array_get_size(x_5);
x_737 = lean_unsigned_to_nat(2u);
x_738 = lean_nat_dec_eq(x_736, x_737);
if (x_738 == 0)
{
lean_object* x_739; 
lean_dec(x_736);
x_739 = lean_box(0);
x_698 = x_739;
goto block_732;
}
else
{
lean_object* x_740; uint8_t x_741; lean_object* x_742; 
lean_dec(x_686);
lean_dec(x_4);
x_740 = lean_unsigned_to_nat(0u);
x_741 = lean_nat_dec_lt(x_740, x_736);
lean_dec(x_736);
lean_inc(x_1);
x_742 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_742, 0, x_1);
if (x_741 == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_5);
x_743 = l_Lean_instInhabitedExpr;
x_744 = l_outOfBounds___rarg(x_743);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_744);
x_745 = lean_grind_internalize(x_744, x_2, x_742, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_685);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_746 = lean_ctor_get(x_745, 1);
lean_inc(x_746);
lean_dec(x_745);
lean_inc(x_1);
x_747 = l_Lean_Meta_Grind_registerParent(x_1, x_744, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_746);
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_747, 1);
lean_inc(x_749);
lean_dec(x_747);
x_750 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_748, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_749);
lean_dec(x_748);
return x_750;
}
else
{
uint8_t x_751; 
lean_dec(x_744);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_751 = !lean_is_exclusive(x_745);
if (x_751 == 0)
{
return x_745;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_752 = lean_ctor_get(x_745, 0);
x_753 = lean_ctor_get(x_745, 1);
lean_inc(x_753);
lean_inc(x_752);
lean_dec(x_745);
x_754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_754, 0, x_752);
lean_ctor_set(x_754, 1, x_753);
return x_754;
}
}
}
else
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_array_fget(x_5, x_740);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_755);
x_756 = lean_grind_internalize(x_755, x_2, x_742, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_685);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_757 = lean_ctor_get(x_756, 1);
lean_inc(x_757);
lean_dec(x_756);
lean_inc(x_1);
x_758 = l_Lean_Meta_Grind_registerParent(x_1, x_755, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_757);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_759, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_760);
lean_dec(x_759);
return x_761;
}
else
{
uint8_t x_762; 
lean_dec(x_755);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_762 = !lean_is_exclusive(x_756);
if (x_762 == 0)
{
return x_756;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_756, 0);
x_764 = lean_ctor_get(x_756, 1);
lean_inc(x_764);
lean_inc(x_763);
lean_dec(x_756);
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
return x_765;
}
}
}
}
}
block_697:
{
lean_object* x_688; lean_object* x_689; 
lean_dec(x_687);
lean_inc(x_1);
x_688 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_688, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_689 = lean_grind_internalize(x_4, x_2, x_688, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_685);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_686, x_690, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_691);
lean_dec(x_690);
lean_dec(x_5);
return x_692;
}
else
{
uint8_t x_693; 
lean_dec(x_686);
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
lean_dec(x_2);
lean_dec(x_1);
x_693 = !lean_is_exclusive(x_689);
if (x_693 == 0)
{
return x_689;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_694 = lean_ctor_get(x_689, 0);
x_695 = lean_ctor_get(x_689, 1);
lean_inc(x_695);
lean_inc(x_694);
lean_dec(x_689);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
return x_696;
}
}
}
block_732:
{
lean_object* x_699; uint8_t x_700; 
lean_dec(x_698);
x_699 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_700 = l_Lean_Expr_isConstOf(x_4, x_699);
if (x_700 == 0)
{
lean_object* x_701; 
lean_dec(x_3);
x_701 = lean_box(0);
x_687 = x_701;
goto block_697;
}
else
{
lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_702 = lean_array_get_size(x_5);
x_703 = lean_unsigned_to_nat(5u);
x_704 = lean_nat_dec_eq(x_702, x_703);
if (x_704 == 0)
{
lean_object* x_705; 
lean_dec(x_702);
lean_dec(x_3);
x_705 = lean_box(0);
x_687 = x_705;
goto block_697;
}
else
{
lean_object* x_706; uint8_t x_707; lean_object* x_708; 
lean_dec(x_686);
lean_dec(x_4);
x_706 = lean_unsigned_to_nat(1u);
x_707 = lean_nat_dec_lt(x_706, x_702);
lean_dec(x_702);
lean_inc(x_1);
x_708 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_708, 0, x_1);
if (x_707 == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_5);
x_709 = l_Lean_instInhabitedExpr;
x_710 = l_outOfBounds___rarg(x_709);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_710);
x_711 = lean_grind_internalize(x_710, x_2, x_708, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_685);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
lean_dec(x_711);
lean_inc(x_1);
x_713 = l_Lean_Meta_Grind_registerParent(x_1, x_710, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_712);
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_714, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_715);
lean_dec(x_714);
return x_716;
}
else
{
uint8_t x_717; 
lean_dec(x_710);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_717 = !lean_is_exclusive(x_711);
if (x_717 == 0)
{
return x_711;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_711, 0);
x_719 = lean_ctor_get(x_711, 1);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_711);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
}
}
else
{
lean_object* x_721; lean_object* x_722; 
x_721 = lean_array_fget(x_5, x_706);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_721);
x_722 = lean_grind_internalize(x_721, x_2, x_708, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_685);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_723 = lean_ctor_get(x_722, 1);
lean_inc(x_723);
lean_dec(x_722);
lean_inc(x_1);
x_724 = l_Lean_Meta_Grind_registerParent(x_1, x_721, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_723);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_727 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_725, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_726);
lean_dec(x_725);
return x_727;
}
else
{
uint8_t x_728; 
lean_dec(x_721);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_728 = !lean_is_exclusive(x_722);
if (x_728 == 0)
{
return x_722;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_722, 0);
x_730 = lean_ctor_get(x_722, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_722);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
}
}
}
}
else
{
uint8_t x_766; 
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
lean_dec(x_1);
x_766 = !lean_is_exclusive(x_684);
if (x_766 == 0)
{
return x_684;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_684, 0);
x_768 = lean_ctor_get(x_684, 1);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_684);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
}
else
{
uint8_t x_770; 
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
lean_dec(x_1);
x_770 = !lean_is_exclusive(x_680);
if (x_770 == 0)
{
return x_680;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_680, 0);
x_772 = lean_ctor_get(x_680, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_680);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_772);
return x_773;
}
}
}
case 9:
{
lean_object* x_774; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_774 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
lean_dec(x_774);
lean_inc(x_1);
x_776 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_775);
x_777 = lean_ctor_get(x_776, 1);
lean_inc(x_777);
lean_dec(x_776);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_778 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_777);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_792; lean_object* x_827; uint8_t x_828; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
lean_dec(x_778);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_780 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_780, 0, x_1);
lean_closure_set(x_780, 1, x_2);
lean_closure_set(x_780, 2, x_3);
x_827 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_828 = l_Lean_Expr_isConstOf(x_4, x_827);
if (x_828 == 0)
{
lean_object* x_829; 
x_829 = lean_box(0);
x_792 = x_829;
goto block_826;
}
else
{
lean_object* x_830; lean_object* x_831; uint8_t x_832; 
x_830 = lean_array_get_size(x_5);
x_831 = lean_unsigned_to_nat(2u);
x_832 = lean_nat_dec_eq(x_830, x_831);
if (x_832 == 0)
{
lean_object* x_833; 
lean_dec(x_830);
x_833 = lean_box(0);
x_792 = x_833;
goto block_826;
}
else
{
lean_object* x_834; uint8_t x_835; lean_object* x_836; 
lean_dec(x_780);
lean_dec(x_4);
x_834 = lean_unsigned_to_nat(0u);
x_835 = lean_nat_dec_lt(x_834, x_830);
lean_dec(x_830);
lean_inc(x_1);
x_836 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_836, 0, x_1);
if (x_835 == 0)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; 
lean_dec(x_5);
x_837 = l_Lean_instInhabitedExpr;
x_838 = l_outOfBounds___rarg(x_837);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_838);
x_839 = lean_grind_internalize(x_838, x_2, x_836, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_779);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_840 = lean_ctor_get(x_839, 1);
lean_inc(x_840);
lean_dec(x_839);
lean_inc(x_1);
x_841 = l_Lean_Meta_Grind_registerParent(x_1, x_838, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_840);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
x_844 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_842, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_843);
lean_dec(x_842);
return x_844;
}
else
{
uint8_t x_845; 
lean_dec(x_838);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_845 = !lean_is_exclusive(x_839);
if (x_845 == 0)
{
return x_839;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_839, 0);
x_847 = lean_ctor_get(x_839, 1);
lean_inc(x_847);
lean_inc(x_846);
lean_dec(x_839);
x_848 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_848, 0, x_846);
lean_ctor_set(x_848, 1, x_847);
return x_848;
}
}
}
else
{
lean_object* x_849; lean_object* x_850; 
x_849 = lean_array_fget(x_5, x_834);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_849);
x_850 = lean_grind_internalize(x_849, x_2, x_836, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_779);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_851 = lean_ctor_get(x_850, 1);
lean_inc(x_851);
lean_dec(x_850);
lean_inc(x_1);
x_852 = l_Lean_Meta_Grind_registerParent(x_1, x_849, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_851);
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_852, 1);
lean_inc(x_854);
lean_dec(x_852);
x_855 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_853, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_854);
lean_dec(x_853);
return x_855;
}
else
{
uint8_t x_856; 
lean_dec(x_849);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_856 = !lean_is_exclusive(x_850);
if (x_856 == 0)
{
return x_850;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_857 = lean_ctor_get(x_850, 0);
x_858 = lean_ctor_get(x_850, 1);
lean_inc(x_858);
lean_inc(x_857);
lean_dec(x_850);
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_857);
lean_ctor_set(x_859, 1, x_858);
return x_859;
}
}
}
}
}
block_791:
{
lean_object* x_782; lean_object* x_783; 
lean_dec(x_781);
lean_inc(x_1);
x_782 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_782, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_783 = lean_grind_internalize(x_4, x_2, x_782, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_779);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
x_786 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_780, x_784, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_785);
lean_dec(x_784);
lean_dec(x_5);
return x_786;
}
else
{
uint8_t x_787; 
lean_dec(x_780);
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
lean_dec(x_2);
lean_dec(x_1);
x_787 = !lean_is_exclusive(x_783);
if (x_787 == 0)
{
return x_783;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_783, 0);
x_789 = lean_ctor_get(x_783, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_783);
x_790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_790, 0, x_788);
lean_ctor_set(x_790, 1, x_789);
return x_790;
}
}
}
block_826:
{
lean_object* x_793; uint8_t x_794; 
lean_dec(x_792);
x_793 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_794 = l_Lean_Expr_isConstOf(x_4, x_793);
if (x_794 == 0)
{
lean_object* x_795; 
lean_dec(x_3);
x_795 = lean_box(0);
x_781 = x_795;
goto block_791;
}
else
{
lean_object* x_796; lean_object* x_797; uint8_t x_798; 
x_796 = lean_array_get_size(x_5);
x_797 = lean_unsigned_to_nat(5u);
x_798 = lean_nat_dec_eq(x_796, x_797);
if (x_798 == 0)
{
lean_object* x_799; 
lean_dec(x_796);
lean_dec(x_3);
x_799 = lean_box(0);
x_781 = x_799;
goto block_791;
}
else
{
lean_object* x_800; uint8_t x_801; lean_object* x_802; 
lean_dec(x_780);
lean_dec(x_4);
x_800 = lean_unsigned_to_nat(1u);
x_801 = lean_nat_dec_lt(x_800, x_796);
lean_dec(x_796);
lean_inc(x_1);
x_802 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_802, 0, x_1);
if (x_801 == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_5);
x_803 = l_Lean_instInhabitedExpr;
x_804 = l_outOfBounds___rarg(x_803);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_804);
x_805 = lean_grind_internalize(x_804, x_2, x_802, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_779);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_806 = lean_ctor_get(x_805, 1);
lean_inc(x_806);
lean_dec(x_805);
lean_inc(x_1);
x_807 = l_Lean_Meta_Grind_registerParent(x_1, x_804, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_806);
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_810 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_808, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_809);
lean_dec(x_808);
return x_810;
}
else
{
uint8_t x_811; 
lean_dec(x_804);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_811 = !lean_is_exclusive(x_805);
if (x_811 == 0)
{
return x_805;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_805, 0);
x_813 = lean_ctor_get(x_805, 1);
lean_inc(x_813);
lean_inc(x_812);
lean_dec(x_805);
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
return x_814;
}
}
}
else
{
lean_object* x_815; lean_object* x_816; 
x_815 = lean_array_fget(x_5, x_800);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_815);
x_816 = lean_grind_internalize(x_815, x_2, x_802, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_779);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_817 = lean_ctor_get(x_816, 1);
lean_inc(x_817);
lean_dec(x_816);
lean_inc(x_1);
x_818 = l_Lean_Meta_Grind_registerParent(x_1, x_815, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_817);
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
lean_dec(x_818);
x_821 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_819, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_820);
lean_dec(x_819);
return x_821;
}
else
{
uint8_t x_822; 
lean_dec(x_815);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_822 = !lean_is_exclusive(x_816);
if (x_822 == 0)
{
return x_816;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = lean_ctor_get(x_816, 0);
x_824 = lean_ctor_get(x_816, 1);
lean_inc(x_824);
lean_inc(x_823);
lean_dec(x_816);
x_825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_825, 0, x_823);
lean_ctor_set(x_825, 1, x_824);
return x_825;
}
}
}
}
}
}
}
else
{
uint8_t x_860; 
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
lean_dec(x_1);
x_860 = !lean_is_exclusive(x_778);
if (x_860 == 0)
{
return x_778;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_778, 0);
x_862 = lean_ctor_get(x_778, 1);
lean_inc(x_862);
lean_inc(x_861);
lean_dec(x_778);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_862);
return x_863;
}
}
}
else
{
uint8_t x_864; 
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
lean_dec(x_1);
x_864 = !lean_is_exclusive(x_774);
if (x_864 == 0)
{
return x_774;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_774, 0);
x_866 = lean_ctor_get(x_774, 1);
lean_inc(x_866);
lean_inc(x_865);
lean_dec(x_774);
x_867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_867, 0, x_865);
lean_ctor_set(x_867, 1, x_866);
return x_867;
}
}
}
case 10:
{
lean_object* x_868; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_868 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_868, 1);
lean_inc(x_869);
lean_dec(x_868);
lean_inc(x_1);
x_870 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_869);
x_871 = lean_ctor_get(x_870, 1);
lean_inc(x_871);
lean_dec(x_870);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_872 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_871);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_886; lean_object* x_921; uint8_t x_922; 
x_873 = lean_ctor_get(x_872, 1);
lean_inc(x_873);
lean_dec(x_872);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_874 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_874, 0, x_1);
lean_closure_set(x_874, 1, x_2);
lean_closure_set(x_874, 2, x_3);
x_921 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_922 = l_Lean_Expr_isConstOf(x_4, x_921);
if (x_922 == 0)
{
lean_object* x_923; 
x_923 = lean_box(0);
x_886 = x_923;
goto block_920;
}
else
{
lean_object* x_924; lean_object* x_925; uint8_t x_926; 
x_924 = lean_array_get_size(x_5);
x_925 = lean_unsigned_to_nat(2u);
x_926 = lean_nat_dec_eq(x_924, x_925);
if (x_926 == 0)
{
lean_object* x_927; 
lean_dec(x_924);
x_927 = lean_box(0);
x_886 = x_927;
goto block_920;
}
else
{
lean_object* x_928; uint8_t x_929; lean_object* x_930; 
lean_dec(x_874);
lean_dec(x_4);
x_928 = lean_unsigned_to_nat(0u);
x_929 = lean_nat_dec_lt(x_928, x_924);
lean_dec(x_924);
lean_inc(x_1);
x_930 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_930, 0, x_1);
if (x_929 == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_dec(x_5);
x_931 = l_Lean_instInhabitedExpr;
x_932 = l_outOfBounds___rarg(x_931);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_932);
x_933 = lean_grind_internalize(x_932, x_2, x_930, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_873);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_934 = lean_ctor_get(x_933, 1);
lean_inc(x_934);
lean_dec(x_933);
lean_inc(x_1);
x_935 = l_Lean_Meta_Grind_registerParent(x_1, x_932, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_934);
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
x_938 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_936, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_937);
lean_dec(x_936);
return x_938;
}
else
{
uint8_t x_939; 
lean_dec(x_932);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_939 = !lean_is_exclusive(x_933);
if (x_939 == 0)
{
return x_933;
}
else
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_940 = lean_ctor_get(x_933, 0);
x_941 = lean_ctor_get(x_933, 1);
lean_inc(x_941);
lean_inc(x_940);
lean_dec(x_933);
x_942 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_942, 0, x_940);
lean_ctor_set(x_942, 1, x_941);
return x_942;
}
}
}
else
{
lean_object* x_943; lean_object* x_944; 
x_943 = lean_array_fget(x_5, x_928);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_943);
x_944 = lean_grind_internalize(x_943, x_2, x_930, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_873);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_945 = lean_ctor_get(x_944, 1);
lean_inc(x_945);
lean_dec(x_944);
lean_inc(x_1);
x_946 = l_Lean_Meta_Grind_registerParent(x_1, x_943, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_945);
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
lean_dec(x_946);
x_949 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_947, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_948);
lean_dec(x_947);
return x_949;
}
else
{
uint8_t x_950; 
lean_dec(x_943);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_950 = !lean_is_exclusive(x_944);
if (x_950 == 0)
{
return x_944;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_944, 0);
x_952 = lean_ctor_get(x_944, 1);
lean_inc(x_952);
lean_inc(x_951);
lean_dec(x_944);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
return x_953;
}
}
}
}
}
block_885:
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_875);
lean_inc(x_1);
x_876 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_876, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_877 = lean_grind_internalize(x_4, x_2, x_876, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_873);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_880 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_874, x_878, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_879);
lean_dec(x_878);
lean_dec(x_5);
return x_880;
}
else
{
uint8_t x_881; 
lean_dec(x_874);
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
lean_dec(x_2);
lean_dec(x_1);
x_881 = !lean_is_exclusive(x_877);
if (x_881 == 0)
{
return x_877;
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_877, 0);
x_883 = lean_ctor_get(x_877, 1);
lean_inc(x_883);
lean_inc(x_882);
lean_dec(x_877);
x_884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_884, 0, x_882);
lean_ctor_set(x_884, 1, x_883);
return x_884;
}
}
}
block_920:
{
lean_object* x_887; uint8_t x_888; 
lean_dec(x_886);
x_887 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_888 = l_Lean_Expr_isConstOf(x_4, x_887);
if (x_888 == 0)
{
lean_object* x_889; 
lean_dec(x_3);
x_889 = lean_box(0);
x_875 = x_889;
goto block_885;
}
else
{
lean_object* x_890; lean_object* x_891; uint8_t x_892; 
x_890 = lean_array_get_size(x_5);
x_891 = lean_unsigned_to_nat(5u);
x_892 = lean_nat_dec_eq(x_890, x_891);
if (x_892 == 0)
{
lean_object* x_893; 
lean_dec(x_890);
lean_dec(x_3);
x_893 = lean_box(0);
x_875 = x_893;
goto block_885;
}
else
{
lean_object* x_894; uint8_t x_895; lean_object* x_896; 
lean_dec(x_874);
lean_dec(x_4);
x_894 = lean_unsigned_to_nat(1u);
x_895 = lean_nat_dec_lt(x_894, x_890);
lean_dec(x_890);
lean_inc(x_1);
x_896 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_896, 0, x_1);
if (x_895 == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec(x_5);
x_897 = l_Lean_instInhabitedExpr;
x_898 = l_outOfBounds___rarg(x_897);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_898);
x_899 = lean_grind_internalize(x_898, x_2, x_896, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_873);
if (lean_obj_tag(x_899) == 0)
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_900 = lean_ctor_get(x_899, 1);
lean_inc(x_900);
lean_dec(x_899);
lean_inc(x_1);
x_901 = l_Lean_Meta_Grind_registerParent(x_1, x_898, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_900);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
lean_dec(x_901);
x_904 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_902, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_903);
lean_dec(x_902);
return x_904;
}
else
{
uint8_t x_905; 
lean_dec(x_898);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_905 = !lean_is_exclusive(x_899);
if (x_905 == 0)
{
return x_899;
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_906 = lean_ctor_get(x_899, 0);
x_907 = lean_ctor_get(x_899, 1);
lean_inc(x_907);
lean_inc(x_906);
lean_dec(x_899);
x_908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_908, 0, x_906);
lean_ctor_set(x_908, 1, x_907);
return x_908;
}
}
}
else
{
lean_object* x_909; lean_object* x_910; 
x_909 = lean_array_fget(x_5, x_894);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_909);
x_910 = lean_grind_internalize(x_909, x_2, x_896, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_873);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_911 = lean_ctor_get(x_910, 1);
lean_inc(x_911);
lean_dec(x_910);
lean_inc(x_1);
x_912 = l_Lean_Meta_Grind_registerParent(x_1, x_909, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_911);
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
x_915 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_913, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_914);
lean_dec(x_913);
return x_915;
}
else
{
uint8_t x_916; 
lean_dec(x_909);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_916 = !lean_is_exclusive(x_910);
if (x_916 == 0)
{
return x_910;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_910, 0);
x_918 = lean_ctor_get(x_910, 1);
lean_inc(x_918);
lean_inc(x_917);
lean_dec(x_910);
x_919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_919, 0, x_917);
lean_ctor_set(x_919, 1, x_918);
return x_919;
}
}
}
}
}
}
}
else
{
uint8_t x_954; 
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
lean_dec(x_1);
x_954 = !lean_is_exclusive(x_872);
if (x_954 == 0)
{
return x_872;
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_955 = lean_ctor_get(x_872, 0);
x_956 = lean_ctor_get(x_872, 1);
lean_inc(x_956);
lean_inc(x_955);
lean_dec(x_872);
x_957 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_957, 0, x_955);
lean_ctor_set(x_957, 1, x_956);
return x_957;
}
}
}
else
{
uint8_t x_958; 
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
lean_dec(x_1);
x_958 = !lean_is_exclusive(x_868);
if (x_958 == 0)
{
return x_868;
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_959 = lean_ctor_get(x_868, 0);
x_960 = lean_ctor_get(x_868, 1);
lean_inc(x_960);
lean_inc(x_959);
lean_dec(x_868);
x_961 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_961, 0, x_959);
lean_ctor_set(x_961, 1, x_960);
return x_961;
}
}
}
default: 
{
lean_object* x_962; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_962 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_963 = lean_ctor_get(x_962, 1);
lean_inc(x_963);
lean_dec(x_962);
lean_inc(x_1);
x_964 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_963);
x_965 = lean_ctor_get(x_964, 1);
lean_inc(x_965);
lean_dec(x_964);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_966 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_965);
if (lean_obj_tag(x_966) == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_980; lean_object* x_1015; uint8_t x_1016; 
x_967 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
lean_dec(x_966);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_968 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_968, 0, x_1);
lean_closure_set(x_968, 1, x_2);
lean_closure_set(x_968, 2, x_3);
x_1015 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4;
x_1016 = l_Lean_Expr_isConstOf(x_4, x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; 
x_1017 = lean_box(0);
x_980 = x_1017;
goto block_1014;
}
else
{
lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; 
x_1018 = lean_array_get_size(x_5);
x_1019 = lean_unsigned_to_nat(2u);
x_1020 = lean_nat_dec_eq(x_1018, x_1019);
if (x_1020 == 0)
{
lean_object* x_1021; 
lean_dec(x_1018);
x_1021 = lean_box(0);
x_980 = x_1021;
goto block_1014;
}
else
{
lean_object* x_1022; uint8_t x_1023; lean_object* x_1024; 
lean_dec(x_968);
lean_dec(x_4);
x_1022 = lean_unsigned_to_nat(0u);
x_1023 = lean_nat_dec_lt(x_1022, x_1018);
lean_dec(x_1018);
lean_inc(x_1);
x_1024 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1024, 0, x_1);
if (x_1023 == 0)
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_5);
x_1025 = l_Lean_instInhabitedExpr;
x_1026 = l_outOfBounds___rarg(x_1025);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1026);
x_1027 = lean_grind_internalize(x_1026, x_2, x_1024, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_967);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1028 = lean_ctor_get(x_1027, 1);
lean_inc(x_1028);
lean_dec(x_1027);
lean_inc(x_1);
x_1029 = l_Lean_Meta_Grind_registerParent(x_1, x_1026, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1028);
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
x_1032 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_1030, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1031);
lean_dec(x_1030);
return x_1032;
}
else
{
uint8_t x_1033; 
lean_dec(x_1026);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1033 = !lean_is_exclusive(x_1027);
if (x_1033 == 0)
{
return x_1027;
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_1034 = lean_ctor_get(x_1027, 0);
x_1035 = lean_ctor_get(x_1027, 1);
lean_inc(x_1035);
lean_inc(x_1034);
lean_dec(x_1027);
x_1036 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1036, 0, x_1034);
lean_ctor_set(x_1036, 1, x_1035);
return x_1036;
}
}
}
else
{
lean_object* x_1037; lean_object* x_1038; 
x_1037 = lean_array_fget(x_5, x_1022);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1037);
x_1038 = lean_grind_internalize(x_1037, x_2, x_1024, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_967);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1039 = lean_ctor_get(x_1038, 1);
lean_inc(x_1039);
lean_dec(x_1038);
lean_inc(x_1);
x_1040 = l_Lean_Meta_Grind_registerParent(x_1, x_1037, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1039);
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec(x_1040);
x_1043 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_1041, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1042);
lean_dec(x_1041);
return x_1043;
}
else
{
uint8_t x_1044; 
lean_dec(x_1037);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1044 = !lean_is_exclusive(x_1038);
if (x_1044 == 0)
{
return x_1038;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1045 = lean_ctor_get(x_1038, 0);
x_1046 = lean_ctor_get(x_1038, 1);
lean_inc(x_1046);
lean_inc(x_1045);
lean_dec(x_1038);
x_1047 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1047, 0, x_1045);
lean_ctor_set(x_1047, 1, x_1046);
return x_1047;
}
}
}
}
}
block_979:
{
lean_object* x_970; lean_object* x_971; 
lean_dec(x_969);
lean_inc(x_1);
x_970 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_970, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_971 = lean_grind_internalize(x_4, x_2, x_970, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_967);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_972 = lean_ctor_get(x_971, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_971, 1);
lean_inc(x_973);
lean_dec(x_971);
x_974 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_968, x_972, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_973);
lean_dec(x_972);
lean_dec(x_5);
return x_974;
}
else
{
uint8_t x_975; 
lean_dec(x_968);
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
lean_dec(x_2);
lean_dec(x_1);
x_975 = !lean_is_exclusive(x_971);
if (x_975 == 0)
{
return x_971;
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_976 = lean_ctor_get(x_971, 0);
x_977 = lean_ctor_get(x_971, 1);
lean_inc(x_977);
lean_inc(x_976);
lean_dec(x_971);
x_978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_978, 0, x_976);
lean_ctor_set(x_978, 1, x_977);
return x_978;
}
}
}
block_1014:
{
lean_object* x_981; uint8_t x_982; 
lean_dec(x_980);
x_981 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2;
x_982 = l_Lean_Expr_isConstOf(x_4, x_981);
if (x_982 == 0)
{
lean_object* x_983; 
lean_dec(x_3);
x_983 = lean_box(0);
x_969 = x_983;
goto block_979;
}
else
{
lean_object* x_984; lean_object* x_985; uint8_t x_986; 
x_984 = lean_array_get_size(x_5);
x_985 = lean_unsigned_to_nat(5u);
x_986 = lean_nat_dec_eq(x_984, x_985);
if (x_986 == 0)
{
lean_object* x_987; 
lean_dec(x_984);
lean_dec(x_3);
x_987 = lean_box(0);
x_969 = x_987;
goto block_979;
}
else
{
lean_object* x_988; uint8_t x_989; lean_object* x_990; 
lean_dec(x_968);
lean_dec(x_4);
x_988 = lean_unsigned_to_nat(1u);
x_989 = lean_nat_dec_lt(x_988, x_984);
lean_dec(x_984);
lean_inc(x_1);
x_990 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_990, 0, x_1);
if (x_989 == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_5);
x_991 = l_Lean_instInhabitedExpr;
x_992 = l_outOfBounds___rarg(x_991);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_992);
x_993 = lean_grind_internalize(x_992, x_2, x_990, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_967);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_994 = lean_ctor_get(x_993, 1);
lean_inc(x_994);
lean_dec(x_993);
lean_inc(x_1);
x_995 = l_Lean_Meta_Grind_registerParent(x_1, x_992, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_994);
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
lean_dec(x_995);
x_998 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_996, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_997);
lean_dec(x_996);
return x_998;
}
else
{
uint8_t x_999; 
lean_dec(x_992);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_999 = !lean_is_exclusive(x_993);
if (x_999 == 0)
{
return x_993;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_1000 = lean_ctor_get(x_993, 0);
x_1001 = lean_ctor_get(x_993, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_993);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
return x_1002;
}
}
}
else
{
lean_object* x_1003; lean_object* x_1004; 
x_1003 = lean_array_fget(x_5, x_988);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1003);
x_1004 = lean_grind_internalize(x_1003, x_2, x_990, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_967);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1005 = lean_ctor_get(x_1004, 1);
lean_inc(x_1005);
lean_dec(x_1004);
lean_inc(x_1);
x_1006 = l_Lean_Meta_Grind_registerParent(x_1, x_1003, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1005);
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
x_1009 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_1007, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1008);
lean_dec(x_1007);
return x_1009;
}
else
{
uint8_t x_1010; 
lean_dec(x_1003);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1010 = !lean_is_exclusive(x_1004);
if (x_1010 == 0)
{
return x_1004;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_1004, 0);
x_1012 = lean_ctor_get(x_1004, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_1004);
x_1013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
return x_1013;
}
}
}
}
}
}
}
else
{
uint8_t x_1048; 
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
lean_dec(x_1);
x_1048 = !lean_is_exclusive(x_966);
if (x_1048 == 0)
{
return x_966;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1049 = lean_ctor_get(x_966, 0);
x_1050 = lean_ctor_get(x_966, 1);
lean_inc(x_1050);
lean_inc(x_1049);
lean_dec(x_966);
x_1051 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1051, 0, x_1049);
lean_ctor_set(x_1051, 1, x_1050);
return x_1051;
}
}
}
else
{
uint8_t x_1052; 
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
lean_dec(x_1);
x_1052 = !lean_is_exclusive(x_962);
if (x_1052 == 0)
{
return x_962;
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1053 = lean_ctor_get(x_962, 0);
x_1054 = lean_ctor_get(x_962, 1);
lean_inc(x_1054);
lean_inc(x_1053);
lean_dec(x_962);
x_1055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1055, 0, x_1053);
lean_ctor_set(x_1055, 1, x_1054);
return x_1055;
}
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__6;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_13, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Internalize", 34, 34);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Internalize.0.Lean.Meta.Grind.internalizeImpl", 77, 77);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(215u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected metavariable during internalization", 46, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n`grind` is not supposed to be used in goals containing metavariables.", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MatchCond", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected metadata found during internalization", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n`grind` uses a pre-processing step that eliminates metadata", 60, 60);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected kernel projection term during internalization", 56, 56);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n`grind` uses a pre-processing step that folds them as projection applications, the pre-processor should have failed to fold this term", 134, 134);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__4;
x_17 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Offset_Main_0__Lean_Meta_Grind_Arith_Offset_setUnsat___spec__1(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_17;
}
case 1:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = 0;
lean_inc(x_1);
x_20 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_19, x_19, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_3);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Meta_Grind_getConfig___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*6 + 6);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = 0;
x_29 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_28, x_28, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
lean_inc(x_1);
x_33 = l_Lean_indentExpr(x_1);
x_34 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_33);
lean_ctor_set(x_24, 0, x_34);
x_35 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__8;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_Grind_reportIssue(x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = 0;
x_40 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_39, x_39, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
lean_inc(x_1);
x_42 = l_Lean_indentExpr(x_1);
x_43 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__8;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_reportIssue(x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_41);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = 0;
x_50 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_49, x_49, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_50;
}
}
}
case 3:
{
uint8_t x_51; 
lean_dec(x_12);
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
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_14, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_14, 0, x_53);
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
case 5:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_58 = l_Lean_Meta_isLitValue(x_1, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__10;
x_63 = lean_unsigned_to_nat(1u);
x_64 = l_Lean_Expr_isAppOfArity(x_1, x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_unsigned_to_nat(0u);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_65);
x_67 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_66);
x_68 = lean_mk_array(x_66, x_67);
x_69 = lean_nat_sub(x_66, x_63);
lean_dec(x_66);
lean_inc(x_1);
x_70 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2(x_1, x_2, x_3, x_1, x_68, x_69, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_61);
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_3);
x_71 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_61);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
lean_dec(x_58);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_73 = l_Lean_Meta_Grind_mkENode(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Meta_Grind_Arith_Offset_internalize(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_74);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_12);
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
x_80 = !lean_is_exclusive(x_58);
if (x_80 == 0)
{
return x_58;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
case 6:
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
lean_dec(x_3);
x_84 = lean_ctor_get(x_14, 1);
lean_inc(x_84);
lean_dec(x_14);
x_85 = 0;
x_86 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_85, x_85, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_84);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_86;
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_119; 
lean_dec(x_3);
x_87 = lean_ctor_get(x_14, 1);
lean_inc(x_87);
lean_dec(x_14);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
x_90 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_91 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_90, x_90, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_87);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_88);
x_119 = l_Lean_Meta_isProp(x_88, x_9, x_10, x_11, x_12, x_92);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_unbox(x_120);
lean_dec(x_120);
x_94 = x_123;
x_95 = x_122;
goto block_118;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_120);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_125 = l_Lean_Meta_isProp(x_1, x_9, x_10, x_11, x_12, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_94 = x_128;
x_95 = x_127;
goto block_118;
}
else
{
uint8_t x_129; 
lean_dec(x_93);
lean_dec(x_89);
lean_dec(x_88);
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
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_125);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_93);
lean_dec(x_89);
lean_dec(x_88);
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
x_133 = !lean_is_exclusive(x_119);
if (x_133 == 0)
{
return x_119;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_119, 0);
x_135 = lean_ctor_get(x_119, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_119);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
block_118:
{
if (x_94 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
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
x_96 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_93;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_93);
lean_inc(x_1);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_98);
lean_inc(x_2);
lean_inc(x_88);
x_99 = lean_grind_internalize(x_88, x_2, x_98, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_95);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_1);
x_101 = l_Lean_Meta_Grind_registerParent(x_1, x_88, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_100);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Expr_hasLooseBVars(x_89);
if (x_103 == 0)
{
lean_object* x_104; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_89);
x_104 = lean_grind_internalize(x_89, x_2, x_98, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_1);
x_106 = l_Lean_Meta_Grind_registerParent(x_1, x_89, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lean_Meta_Grind_propagateUp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_107);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_89);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_98);
lean_dec(x_89);
lean_dec(x_2);
x_113 = l_Lean_Meta_Grind_propagateUp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_98);
lean_dec(x_89);
lean_dec(x_88);
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
x_114 = !lean_is_exclusive(x_99);
if (x_114 == 0)
{
return x_99;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_99, 0);
x_116 = lean_ctor_get(x_99, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_99);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
case 8:
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; 
lean_dec(x_3);
x_137 = lean_ctor_get(x_14, 1);
lean_inc(x_137);
lean_dec(x_14);
x_138 = 0;
x_139 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_138, x_138, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_137);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_139;
}
case 10:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_3);
x_140 = lean_ctor_get(x_14, 1);
lean_inc(x_140);
lean_dec(x_14);
x_141 = l_Lean_Meta_Grind_getConfig___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*6 + 6);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = 0;
x_146 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_145, x_145, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_144);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_146;
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_141);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_141, 1);
x_149 = lean_ctor_get(x_141, 0);
lean_dec(x_149);
lean_inc(x_1);
x_150 = l_Lean_indentExpr(x_1);
x_151 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__12;
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_150);
lean_ctor_set(x_141, 0, x_151);
x_152 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__14;
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_141);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Meta_Grind_reportIssue(x_153, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = 0;
x_157 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_156, x_156, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_155);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_141, 1);
lean_inc(x_158);
lean_dec(x_141);
lean_inc(x_1);
x_159 = l_Lean_indentExpr(x_1);
x_160 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__12;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__14;
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Meta_Grind_reportIssue(x_163, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = 0;
x_167 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_166, x_166, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_165);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_167;
}
}
}
case 11:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_dec(x_3);
x_168 = lean_ctor_get(x_14, 1);
lean_inc(x_168);
lean_dec(x_14);
x_169 = l_Lean_Meta_Grind_getConfig___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_170, sizeof(void*)*6 + 6);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = 0;
x_174 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_173, x_173, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_172);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_174;
}
else
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_169);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; 
x_176 = lean_ctor_get(x_169, 1);
x_177 = lean_ctor_get(x_169, 0);
lean_dec(x_177);
lean_inc(x_1);
x_178 = l_Lean_indentExpr(x_1);
x_179 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__16;
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_178);
lean_ctor_set(x_169, 0, x_179);
x_180 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__18;
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_169);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Meta_Grind_reportIssue(x_181, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_176);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = 0;
x_185 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_184, x_184, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_183);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; 
x_186 = lean_ctor_get(x_169, 1);
lean_inc(x_186);
lean_dec(x_169);
lean_inc(x_1);
x_187 = l_Lean_indentExpr(x_1);
x_188 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__16;
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__18;
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_Meta_Grind_reportIssue(x_191, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_186);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = 0;
x_195 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_194, x_194, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_193);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_195;
}
}
}
default: 
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_3);
x_196 = lean_ctor_get(x_14, 1);
lean_inc(x_196);
lean_dec(x_14);
x_197 = l_Lean_Meta_Grind_mkENode(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_196);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_12);
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
x_198 = !lean_is_exclusive(x_14);
if (x_198 == 0)
{
return x_14;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_14, 0);
x_200 = lean_ctor_get(x_14, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_14);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__2;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
x_26 = l_Lean_MessageData_ofExpr(x_1);
x_27 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_27);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_14, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3(x_1, x_2, x_3, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_free_object(x_15);
lean_dec(x_12);
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
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_1);
x_40 = l_Lean_MessageData_ofExpr(x_1);
x_41 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_14, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3(x_1, x_2, x_3, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_46);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_12);
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
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_50 = x_38;
} else {
 lean_dec_ref(x_38);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Offset_internalize(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("already internalized: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_grind_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 7);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 8);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 9);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 10);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_10, sizeof(void*)*12);
x_25 = lean_ctor_get(x_10, 11);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_10, sizeof(void*)*12 + 1);
x_27 = lean_nat_dec_eq(x_16, x_17);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_29 = lean_ctor_get(x_10, 11);
lean_dec(x_29);
x_30 = lean_ctor_get(x_10, 10);
lean_dec(x_30);
x_31 = lean_ctor_get(x_10, 9);
lean_dec(x_31);
x_32 = lean_ctor_get(x_10, 8);
lean_dec(x_32);
x_33 = lean_ctor_get(x_10, 7);
lean_dec(x_33);
x_34 = lean_ctor_get(x_10, 6);
lean_dec(x_34);
x_35 = lean_ctor_get(x_10, 5);
lean_dec(x_35);
x_36 = lean_ctor_get(x_10, 4);
lean_dec(x_36);
x_37 = lean_ctor_get(x_10, 3);
lean_dec(x_37);
x_38 = lean_ctor_get(x_10, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_10, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_10, 0);
lean_dec(x_40);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_16, x_41);
lean_dec(x_16);
lean_ctor_set(x_10, 3, x_42);
x_43 = l_Lean_Meta_Grind_alreadyInternalized(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(0);
x_48 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4(x_1, x_2, x_3, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_43, 1);
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_52 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1;
x_53 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_43);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_box(0);
x_58 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_3, x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 1);
x_61 = lean_ctor_get(x_53, 0);
lean_dec(x_61);
x_62 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_1);
x_64 = l_Lean_MessageData_ofExpr(x_1);
x_65 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3;
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_64);
lean_ctor_set(x_53, 0, x_65);
x_66 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_66);
lean_ctor_set(x_43, 0, x_53);
x_67 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_52, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_3, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
lean_dec(x_68);
return x_70;
}
else
{
uint8_t x_71; 
lean_free_object(x_53);
lean_free_object(x_43);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_62);
if (x_71 == 0)
{
return x_62;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_62, 0);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_62);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_53, 1);
lean_inc(x_75);
lean_dec(x_53);
x_76 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_1);
x_78 = l_Lean_MessageData_ofExpr(x_1);
x_79 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_81);
lean_ctor_set(x_43, 0, x_80);
x_82 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_52, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_77);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_3, x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
lean_dec(x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_43);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_88 = x_76;
} else {
 lean_dec_ref(x_76);
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
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_43, 1);
lean_inc(x_90);
lean_dec(x_43);
x_91 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1;
x_92 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_box(0);
x_97 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_3, x_96, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_1);
x_102 = l_Lean_MessageData_ofExpr(x_1);
x_103 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3;
if (lean_is_scalar(x_99)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_99;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_91, x_106, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_101);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_3, x_108, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_109);
lean_dec(x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_99);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_111 = lean_ctor_get(x_100, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_113 = x_100;
} else {
 lean_dec_ref(x_100);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_10);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_16, x_115);
lean_dec(x_16);
x_117 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_117, 0, x_13);
lean_ctor_set(x_117, 1, x_14);
lean_ctor_set(x_117, 2, x_15);
lean_ctor_set(x_117, 3, x_116);
lean_ctor_set(x_117, 4, x_17);
lean_ctor_set(x_117, 5, x_18);
lean_ctor_set(x_117, 6, x_19);
lean_ctor_set(x_117, 7, x_20);
lean_ctor_set(x_117, 8, x_21);
lean_ctor_set(x_117, 9, x_22);
lean_ctor_set(x_117, 10, x_23);
lean_ctor_set(x_117, 11, x_25);
lean_ctor_set_uint8(x_117, sizeof(void*)*12, x_24);
lean_ctor_set_uint8(x_117, sizeof(void*)*12 + 1, x_26);
x_118 = l_Lean_Meta_Grind_alreadyInternalized(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_117, x_11, x_12);
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
x_123 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4(x_1, x_2, x_3, x_122, x_4, x_5, x_6, x_7, x_8, x_9, x_117, x_11, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_2);
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
x_126 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1;
x_127 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_126, x_4, x_5, x_6, x_7, x_8, x_9, x_117, x_11, x_124);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_125);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_box(0);
x_132 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_3, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_117, x_11, x_130);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
x_135 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_117, x_11, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
lean_inc(x_1);
x_137 = l_Lean_MessageData_ofExpr(x_1);
x_138 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3;
if (lean_is_scalar(x_134)) {
 x_139 = lean_alloc_ctor(7, 2, 0);
} else {
 x_139 = x_134;
 lean_ctor_set_tag(x_139, 7);
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
if (lean_is_scalar(x_125)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_125;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_126, x_141, x_4, x_5, x_6, x_7, x_8, x_9, x_117, x_11, x_136);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_3, x_143, x_4, x_5, x_6, x_7, x_8, x_9, x_117, x_11, x_144);
lean_dec(x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_134);
lean_dec(x_125);
lean_dec(x_117);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_ctor_get(x_135, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_148 = x_135;
} else {
 lean_dec_ref(x_135);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
}
else
{
lean_object* x_150; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_150;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__1___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Beta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1();
l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8);
l_Lean_Meta_Grind_addCongrTable___closed__1 = _init_l_Lean_Meta_Grind_addCongrTable___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__1);
l_Lean_Meta_Grind_addCongrTable___closed__2 = _init_l_Lean_Meta_Grind_addCongrTable___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__2);
l_Lean_Meta_Grind_addCongrTable___closed__3 = _init_l_Lean_Meta_Grind_addCongrTable___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__3);
l_Lean_Meta_Grind_addCongrTable___closed__4 = _init_l_Lean_Meta_Grind_addCongrTable___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__4);
l_Lean_Meta_Grind_addCongrTable___closed__5 = _init_l_Lean_Meta_Grind_addCongrTable___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__5);
l_Lean_Meta_Grind_addCongrTable___closed__6 = _init_l_Lean_Meta_Grind_addCongrTable___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__6);
l_Lean_Meta_Grind_addCongrTable___closed__7 = _init_l_Lean_Meta_Grind_addCongrTable___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__7);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__5);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__5);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___closed__7);
l_Lean_Meta_Grind_activateTheorem___closed__1 = _init_l_Lean_Meta_Grind_activateTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__1);
l_Lean_Meta_Grind_activateTheorem___closed__2 = _init_l_Lean_Meta_Grind_activateTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__2);
l_Lean_Meta_Grind_activateTheorem___closed__3 = _init_l_Lean_Meta_Grind_activateTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__3);
l_Lean_Meta_Grind_activateTheorem___closed__4 = _init_l_Lean_Meta_Grind_activateTheorem___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__4);
l_Lean_Meta_Grind_activateTheorem___closed__5 = _init_l_Lean_Meta_Grind_activateTheorem___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__5);
l_Lean_Meta_Grind_activateTheorem___closed__6 = _init_l_Lean_Meta_Grind_activateTheorem___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__6);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4);
l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__1 = _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__1);
l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__2 = _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__2);
l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__3 = _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__3);
l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__4 = _init_l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_propagateUnitLike___spec__1___closed__4);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__3 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__3);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__2___closed__4);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__2);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__3);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__4);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__5);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___spec__3___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__5);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__7);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__8);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__9);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__10);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__11);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__12);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__13);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__14 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__14);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__15);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__16 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__16);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__17 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__17);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__18 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__3___closed__18);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___lambda__4___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeImpl___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
