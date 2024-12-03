// Lean compiler output
// Module: Lean.Meta.Tactic.Cases
// Imports: Lean.Meta.AppBuilder Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Injection Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Acyclic Lean.Meta.Tactic.UnifyEq
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
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
static lean_object* l_Lean_MVarId_byCasesDec___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___closed__3;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__7;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_byCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_unifyEqs_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__4;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object*, lean_object*, lean_object*, size_t, size_t);
extern lean_object* l_Lean_casesOnSuffix;
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__12;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__10;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwNestedTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__1;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__1;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__57(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__6;
lean_object* l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___closed__2;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_substEqs___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__1;
static lean_object* l_Lean_MVarId_byCases___closed__1;
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__10;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__1;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__11;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_acyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794_(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__9;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__8;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
lean_object* l_Lean_MVarId_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_byCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__13;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__58___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__58(lean_object*, size_t, size_t);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_MVarId_casesRec___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCasesDec___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesRec___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__5;
static lean_object* l_Lean_MVarId_byCasesDec___closed__5;
static lean_object* l_Lean_MVarId_byCasesDec___closed__2;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___closed__4;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getInductiveUniverseAndParams___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___closed__1;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_ensureAtMostOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__2;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCasesDec___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__15;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__8;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_mkEM(lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__6;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__14;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_MVarId_casesRec___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__57___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_casesAnd___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_MVarId_byCases___closed__4;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__3;
static lean_object* l_Lean_MVarId_casesAnd___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__7;
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__6;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to compile pattern matching, inductive type expected", 59, 59);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_indentExpr(x_1);
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnfD(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_getAppFn(x_8);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Environment_find_x3f(x_17, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_13);
lean_dec(x_12);
x_19 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 5)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_8, x_22);
x_24 = l_Lean_Meta_getInductiveUniverseAndParams___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_8, x_25, x_27);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Array_extract___rarg(x_28, x_22, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_13, 0, x_31);
return x_13;
}
else
{
lean_object* x_32; 
lean_dec(x_20);
lean_free_object(x_13);
lean_dec(x_12);
x_32 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Environment_find_x3f(x_35, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_12);
x_37 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
if (lean_obj_tag(x_38) == 5)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_8, x_40);
x_42 = l_Lean_Meta_getInductiveUniverseAndParams___closed__1;
lean_inc(x_41);
x_43 = lean_mk_array(x_41, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_41, x_44);
lean_dec(x_41);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_8, x_43, x_45);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = l_Array_extract___rarg(x_46, x_40, x_47);
lean_dec(x_47);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_34);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_38);
lean_dec(x_12);
x_51 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_10);
x_52 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refl", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_9);
x_17 = l_Lean_Meta_isExprDefEq(x_9, x_12, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
lean_inc(x_23);
x_25 = l_Lean_Expr_const___override(x_24, x_23);
lean_inc(x_1);
lean_inc(x_9);
x_26 = l_Lean_mkApp4(x_25, x_9, x_1, x_12, x_2);
x_27 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
x_28 = l_Lean_Expr_const___override(x_27, x_23);
x_29 = l_Lean_mkAppB(x_28, x_9, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
lean_inc(x_33);
x_35 = l_Lean_Expr_const___override(x_34, x_33);
lean_inc(x_1);
lean_inc(x_9);
x_36 = l_Lean_mkApp4(x_35, x_9, x_1, x_12, x_2);
x_37 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
x_38 = l_Lean_Expr_const___override(x_37, x_33);
x_39 = l_Lean_mkAppB(x_38, x_9, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_31);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_17, 0);
lean_dec(x_43);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
lean_inc(x_45);
x_47 = l_Lean_Expr_const___override(x_46, x_45);
lean_inc(x_1);
lean_inc(x_9);
x_48 = l_Lean_mkApp3(x_47, x_9, x_1, x_2);
x_49 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7;
x_50 = l_Lean_Expr_const___override(x_49, x_45);
x_51 = l_Lean_mkAppB(x_50, x_9, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_17, 0, x_52);
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_dec(x_17);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_15);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
lean_inc(x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_55);
lean_inc(x_1);
lean_inc(x_9);
x_58 = l_Lean_mkApp3(x_57, x_9, x_1, x_2);
x_59 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7;
x_60 = l_Lean_Expr_const___override(x_59, x_55);
x_61 = l_Lean_mkAppB(x_60, x_9, x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
return x_17;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_14);
if (x_68 == 0)
{
return x_14;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_14, 0);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_11);
if (x_72 == 0)
{
return x_11;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_11, 0);
x_74 = lean_ctor_get(x_11, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_8);
if (x_76 == 0)
{
return x_8;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_8, 0);
x_78 = lean_ctor_get(x_8, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_8);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = lean_array_push(x_2, x_8);
x_17 = lean_array_push(x_3, x_4);
x_18 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_4, x_15);
lean_dec(x_15);
x_17 = lean_array_fget(x_1, x_4);
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_instInhabitedExpr;
x_19 = l_outOfBounds___rarg(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(x_17, x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_6);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_1);
lean_closure_set(x_25, 5, x_2);
lean_closure_set(x_25, 6, x_3);
x_26 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2;
x_27 = 0;
x_28 = 0;
x_29 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__3___rarg(x_26, x_27, x_23, x_25, x_28, x_7, x_8, x_9, x_10, x_22);
return x_29;
}
else
{
uint8_t x_30; 
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
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
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
x_34 = lean_array_fget(x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(x_17, x_34, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_40, 0, x_4);
lean_closure_set(x_40, 1, x_5);
lean_closure_set(x_40, 2, x_6);
lean_closure_set(x_40, 3, x_39);
lean_closure_set(x_40, 4, x_1);
lean_closure_set(x_40, 5, x_2);
lean_closure_set(x_40, 6, x_3);
x_41 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2;
x_42 = 0;
x_43 = 0;
x_44 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__3___rarg(x_41, x_42, x_38, x_40, x_43, x_7, x_8, x_9, x_10, x_37);
return x_44;
}
else
{
uint8_t x_45; 
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
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
x_11 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg(x_1, x_2, x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_3, x_11, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkForallFVars(x_2, x_17, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
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
uint8_t x_31; 
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
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
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lambda__1___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg(x_3, x_2, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid number of targets #", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", motive expects #", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_25, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_10);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_generalizeTargetsEq___lambda__2(x_1, x_3, x_2, x_31, x_5, x_6, x_7, x_8, x_9);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lambda__3___boxed), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
x_13 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_4, x_12, x_13, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_1);
x_19 = l_Lean_MVarId_getTag(x_1, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_20, x_5, x_6, x_7, x_8, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = l_Lean_mkAppN(x_23, x_3);
lean_dec(x_3);
x_26 = l_Lean_mkAppN(x_25, x_18);
lean_dec(x_18);
x_27 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_26, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l_Lean_Expr_mvarId_x21(x_23);
lean_dec(x_23);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Expr_mvarId_x21(x_23);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generalizeTargets", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_generalizeTargetsEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Meta_generalizeTargetsEq___closed__2;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lambda__4), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_2);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_generalizeTargetsEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_generalizeTargetsEq___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_generalizeTargetsEq___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_1, x_10);
lean_inc(x_2);
x_17 = l_Lean_MVarId_getType(x_2, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_2);
x_20 = l_Lean_MVarId_getTag(x_2, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
x_24 = 1;
x_25 = 1;
x_26 = l_Lean_Meta_mkForallFVars(x_16, x_18, x_23, x_24, x_25, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_mk(x_30);
x_32 = l_Lean_Meta_mkForallFVars(x_31, x_27, x_23, x_24, x_25, x_11, x_12, x_13, x_14, x_28);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_mkForallFVars(x_4, x_33, x_23, x_24, x_25, x_11, x_12, x_13, x_14, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 2;
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_6, x_36, x_38, x_21, x_39, x_11, x_12, x_13, x_14, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_41);
x_43 = l_Lean_mkAppN(x_41, x_7);
x_44 = l_Lean_Expr_app___override(x_43, x_8);
x_45 = l_Lean_mkAppN(x_44, x_9);
x_46 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_2, x_45, x_11, x_12, x_13, x_14, x_42);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Expr_mvarId_x21(x_41);
lean_dec(x_41);
x_49 = lean_array_get_size(x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_50 = l_Lean_Meta_introNCore(x_48, x_49, x_29, x_23, x_24, x_11, x_12, x_13, x_14, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lean_Meta_intro1Core(x_54, x_24, x_11, x_12, x_13, x_14, x_52);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_array_get_size(x_16);
lean_dec(x_16);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_55, 0, x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_55, 0);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_55);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_array_get_size(x_16);
lean_dec(x_16);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_53);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_53);
lean_dec(x_16);
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
return x_55;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_55, 0);
x_71 = lean_ctor_get(x_55, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_55);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_73 = !lean_is_exclusive(x_50);
if (x_73 == 0)
{
return x_50;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_50, 0);
x_75 = lean_ctor_get(x_50, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_50);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_35);
if (x_77 == 0)
{
return x_35;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_35, 0);
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_35);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_32);
if (x_81 == 0)
{
return x_32;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_32, 0);
x_83 = lean_ctor_get(x_32, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_32);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_26);
if (x_85 == 0)
{
return x_26;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_26, 0);
x_87 = lean_ctor_get(x_26, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_26);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_20);
if (x_89 == 0)
{
return x_20;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_20, 0);
x_91 = lean_ctor_get(x_20, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_20);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_17);
if (x_93 == 0)
{
return x_17;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_17, 0);
x_95 = lean_ctor_get(x_17, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_17);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_LocalDecl_toExpr(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_15);
x_16 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(x_15, x_2, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_array_push(x_9, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed), 15, 9);
lean_closure_set(x_22, 0, x_8);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_5);
lean_closure_set(x_22, 5, x_6);
lean_closure_set(x_22, 6, x_7);
lean_closure_set(x_22, 7, x_15);
lean_closure_set(x_22, 8, x_21);
x_23 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2;
x_24 = 0;
x_25 = 0;
x_26 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__3___rarg(x_23, x_24, x_19, x_22, x_25, x_10, x_11, x_12, x_13, x_18);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_13);
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
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed), 14, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_7);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
x_14 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg(x_6, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = l_Lean_mkAppN(x_1, x_7);
x_15 = l_Lean_LocalDecl_userName(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3), 12, 6);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_7);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
x_17 = 0;
x_18 = 0;
x_19 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__3___rarg(x_15, x_17, x_14, x_16, x_18, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_nat_sub(x_14, x_15);
x_17 = l_Array_extract___rarg(x_1, x_16, x_14);
lean_dec(x_14);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_extract___rarg(x_1, x_19, x_18);
x_21 = l_Lean_mkAppN(x_3, x_20);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_22 = lean_infer_type(x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed), 13, 6);
lean_closure_set(x_25, 0, x_21);
lean_closure_set(x_25, 1, x_4);
lean_closure_set(x_25, 2, x_5);
lean_closure_set(x_25, 3, x_6);
lean_closure_set(x_25, 4, x_7);
lean_closure_set(x_25, 5, x_17);
x_26 = 0;
x_27 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_23, x_25, x_26, x_9, x_10, x_11, x_12, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed inductive datatype", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_nat_add(x_16, x_17);
x_19 = lean_nat_dec_eq(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_20 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__4;
x_21 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_5, x_20, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
x_26 = lean_box(0);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_26, x_10, x_11, x_12, x_13, x_14);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inductive type expected", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("indexed inductive type expected", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 4:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_st_ref_get(x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Environment_find_x3f(x_18, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
x_21 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_20, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__8;
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_27, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(x_7, x_23, x_6, x_5, x_1, x_2, x_3, x_4, x_33, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_23);
lean_dec(x_7);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_35, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_36;
}
}
}
case 5:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_array_set(x_7, x_8, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_8, x_40);
lean_dec(x_8);
x_6 = x_37;
x_7 = x_39;
x_8 = x_41;
goto _start;
}
default: 
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_43, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generalizeIndices", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = l_Lean_Meta_getLocalInstances(x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_inc(x_1);
x_13 = l_Lean_MVarId_checkNotAssigned(x_1, x_12, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_3);
x_15 = l_Lean_FVarId_getDecl(x_2, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = lean_whnf(x_18, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_20, x_22);
x_24 = l_Lean_Meta_getInductiveUniverseAndParams___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(x_1, x_8, x_10, x_12, x_16, x_20, x_25, x_27, x_3, x_4, x_5, x_6, x_21);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Environment_find_x3f(x_15, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 5)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_get_size(x_4);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_eq(x_20, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1;
x_29 = l_Lean_Name_str___override(x_27, x_28);
x_30 = l_Lean_Environment_find_x3f(x_1, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_19, 4);
lean_inc(x_35);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_List_lengthTRAux___rarg(x_35, x_36);
lean_dec(x_35);
x_38 = lean_nat_sub(x_20, x_21);
lean_dec(x_21);
x_39 = l_Array_extract___rarg(x_4, x_38, x_20);
lean_dec(x_20);
x_40 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_2);
lean_ctor_set(x_40, 4, x_3);
lean_ctor_set(x_40, 5, x_4);
lean_ctor_set(x_40, 6, x_39);
lean_ctor_set(x_30, 0, x_40);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_41; 
lean_free_object(x_30);
lean_dec(x_33);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_box(0);
lean_ctor_set(x_12, 0, x_41);
return x_12;
}
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
lean_dec(x_30);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_19, 4);
lean_inc(x_44);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_List_lengthTRAux___rarg(x_44, x_45);
lean_dec(x_44);
x_47 = lean_nat_sub(x_20, x_21);
lean_dec(x_21);
x_48 = l_Array_extract___rarg(x_4, x_47, x_20);
lean_dec(x_20);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_2);
lean_ctor_set(x_49, 4, x_3);
lean_ctor_set(x_49, 5, x_4);
lean_ctor_set(x_49, 6, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_12, 0, x_50);
return x_12;
}
else
{
lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_box(0);
lean_ctor_set(x_12, 0, x_51);
return x_12;
}
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
lean_ctor_set(x_12, 0, x_52);
return x_12;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Environment_find_x3f(x_55, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
if (lean_obj_tag(x_59) == 5)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_array_get_size(x_4);
x_62 = lean_ctor_get(x_60, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_63);
x_65 = lean_nat_dec_eq(x_61, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_54);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1;
x_71 = l_Lean_Name_str___override(x_69, x_70);
x_72 = l_Lean_Environment_find_x3f(x_1, x_71);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_54);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
if (lean_obj_tag(x_75) == 1)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_60, 4);
lean_inc(x_78);
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_List_lengthTRAux___rarg(x_78, x_79);
lean_dec(x_78);
x_81 = lean_nat_sub(x_61, x_62);
lean_dec(x_62);
x_82 = l_Array_extract___rarg(x_4, x_81, x_61);
lean_dec(x_61);
x_83 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_83, 0, x_60);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_2);
lean_ctor_set(x_83, 4, x_3);
lean_ctor_set(x_83, 5, x_4);
lean_ctor_set(x_83, 6, x_82);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_54);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_54);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_59);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_54);
return x_89;
}
}
}
}
case 5:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_dec(x_3);
x_92 = lean_array_set(x_4, x_5, x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_sub(x_5, x_93);
lean_dec(x_5);
x_3 = x_90;
x_4 = x_92;
x_5 = x_94;
goto _start;
}
default: 
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_10);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
lean_inc(x_11);
x_13 = l_Lean_Environment_contains(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
lean_inc(x_11);
x_16 = l_Lean_Environment_contains(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; 
lean_free_object(x_7);
lean_inc(x_2);
x_18 = l_Lean_FVarId_getDecl(x_1, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = lean_whnf(x_21, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_23, x_25);
x_27 = l_Lean_Meta_getInductiveUniverseAndParams___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
x_31 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(x_11, x_19, x_23, x_28, x_30, x_2, x_3, x_4, x_5, x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
lean_inc(x_42);
x_44 = l_Lean_Environment_contains(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
lean_inc(x_42);
x_48 = l_Lean_Environment_contains(x_42, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
else
{
lean_object* x_51; 
lean_inc(x_2);
x_51 = l_Lean_FVarId_getDecl(x_1, x_2, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_LocalDecl_type(x_52);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_55 = lean_whnf(x_54, x_2, x_3, x_4, x_5, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_56, x_58);
x_60 = l_Lean_Meta_getInductiveUniverseAndParams___closed__1;
lean_inc(x_59);
x_61 = lean_mk_array(x_59, x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_59, x_62);
lean_dec(x_59);
x_64 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(x_42, x_52, x_56, x_61, x_63, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_52);
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_67 = x_55;
} else {
 lean_dec_ref(x_55);
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
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_51, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_51, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_71 = x_51;
} else {
 lean_dec_ref(x_51);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_nat_add(x_11, x_10);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_12);
x_14 = lean_array_fget(x_2, x_3);
x_15 = lean_array_fget(x_2, x_13);
lean_dec(x_13);
x_16 = lean_expr_eqv(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
x_4 = lean_box(0);
x_6 = x_11;
x_7 = lean_box(0);
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = 0;
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
lean_inc(x_11);
x_12 = l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_1, x_2, x_11, lean_box(0), x_11, x_11, lean_box(0));
lean_dec(x_11);
if (x_12 == 0)
{
x_4 = x_9;
x_5 = lean_box(0);
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_4, x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_12, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_6, x_11, x_12);
return x_13;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_5, x_1, x_11, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_20, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_20);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_29);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = l_Lean_MetavarContext_getDecl(x_33, x_20);
lean_dec(x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_36);
lean_dec(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_41, x_40);
return x_42;
}
}
case 5:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_getAppFn(x_3);
x_44 = l_Lean_Expr_isMVar(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_3);
x_46 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_getAppFn(x_47);
x_50 = lean_expr_eqv(x_49, x_43);
lean_dec(x_43);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_3);
x_3 = x_47;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_48);
return x_52;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
lean_dec(x_3);
x_55 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_53, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_54, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_54);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
lean_dec(x_3);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_64, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_65, x_69);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_65);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_dec(x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 8:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_75, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_76, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_77, x_85);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_77);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_dec(x_76);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_78, 0);
lean_dec(x_92);
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 10:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_95, x_4);
return x_96;
}
case 11:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
lean_dec(x_3);
x_98 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_97, x_4);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
x_99 = 0;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_4, x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_12, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_6, x_11, x_12);
return x_13;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_5, x_1, x_11, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_20, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_20);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_29);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = l_Lean_MetavarContext_getDecl(x_33, x_20);
lean_dec(x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_36);
lean_dec(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_41, x_40);
return x_42;
}
}
case 5:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_getAppFn(x_3);
x_44 = l_Lean_Expr_isMVar(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_3, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_3);
x_46 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_getAppFn(x_47);
x_50 = lean_expr_eqv(x_49, x_43);
lean_dec(x_43);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_3);
x_3 = x_47;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_3, x_48);
return x_52;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
lean_dec(x_3);
x_55 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_53, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_54, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_54);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
lean_dec(x_3);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_64, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_65, x_69);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_65);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_dec(x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 8:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_75, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_76, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_77, x_85);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_77);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_dec(x_76);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_78, 0);
lean_dec(x_92);
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 10:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_95, x_4);
return x_96;
}
case 11:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
lean_dec(x_3);
x_98 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_97, x_4);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
x_99 = 0;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_4, x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_12, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_6, x_11, x_12);
return x_13;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_5, x_1, x_11, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_20, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_20);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_29);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = l_Lean_MetavarContext_getDecl(x_33, x_20);
lean_dec(x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_36);
lean_dec(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_41, x_40);
return x_42;
}
}
case 5:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_getAppFn(x_3);
x_44 = l_Lean_Expr_isMVar(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_3, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_3);
x_46 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_getAppFn(x_47);
x_50 = lean_expr_eqv(x_49, x_43);
lean_dec(x_43);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_3);
x_3 = x_47;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_3, x_48);
return x_52;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
lean_dec(x_3);
x_55 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_53, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_54, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_54);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
lean_dec(x_3);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_64, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_65, x_69);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_65);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_dec(x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 8:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_75, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_76, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_77, x_85);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_77);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_dec(x_76);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_78, 0);
lean_dec(x_92);
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 10:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_95, x_4);
return x_96;
}
case 11:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
lean_dec(x_3);
x_98 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_97, x_4);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
x_99 = 0;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_4, x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_12, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(x_1, x_2, x_6, x_11, x_12);
return x_13;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_5, x_1, x_11, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_20, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_20);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_29);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = l_Lean_MetavarContext_getDecl(x_33, x_20);
lean_dec(x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_36);
lean_dec(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_41, x_40);
return x_42;
}
}
case 5:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_getAppFn(x_3);
x_44 = l_Lean_Expr_isMVar(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_3);
x_46 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_getAppFn(x_47);
x_50 = lean_expr_eqv(x_49, x_43);
lean_dec(x_43);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_3);
x_3 = x_47;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_48);
return x_52;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
lean_dec(x_3);
x_55 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_53, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_54, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_54);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
lean_dec(x_3);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_64, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_65, x_69);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_65);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_dec(x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 8:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_75, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_76, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_77, x_85);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_77);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_dec(x_76);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_78, 0);
lean_dec(x_92);
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 10:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_95, x_4);
return x_96;
}
case 11:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
lean_dec(x_3);
x_98 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_97, x_4);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
x_99 = 0;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_4, x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(x_1, x_2, x_12, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(x_1, x_2, x_6, x_11, x_12);
return x_13;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_5, x_1, x_11, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_20, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_20);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_29);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = l_Lean_MetavarContext_getDecl(x_33, x_20);
lean_dec(x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_36);
lean_dec(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_41, x_40);
return x_42;
}
}
case 5:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_getAppFn(x_3);
x_44 = l_Lean_Expr_isMVar(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_3);
x_46 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_getAppFn(x_47);
x_50 = lean_expr_eqv(x_49, x_43);
lean_dec(x_43);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_3);
x_3 = x_47;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_48);
return x_52;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
lean_dec(x_3);
x_55 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_53, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_54, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_54);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
lean_dec(x_3);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_64, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_65, x_69);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_65);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_dec(x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 8:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_75, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_76, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_77, x_85);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_77);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_dec(x_76);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_78, 0);
lean_dec(x_92);
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 10:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_95, x_4);
return x_96;
}
case 11:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
lean_dec(x_3);
x_98 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_97, x_4);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
x_99 = 0;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(x_1, x_2, x_4, x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 0;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(x_1, x_2, x_12, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_fvarId(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_12, x_1, x_16, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(x_1, x_2, x_6, x_11, x_12);
return x_13;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_2);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_5, x_1, x_11, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_20, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_MetavarContext_getDecl(x_26, x_20);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(x_1, x_2, x_29);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = l_Lean_MetavarContext_getDecl(x_33, x_20);
lean_dec(x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(x_1, x_2, x_36);
lean_dec(x_36);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_41, x_40);
return x_42;
}
}
case 5:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_getAppFn(x_3);
x_44 = l_Lean_Expr_isMVar(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
x_45 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_3);
x_46 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_getAppFn(x_47);
x_50 = lean_expr_eqv(x_49, x_43);
lean_dec(x_43);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_3);
x_3 = x_47;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_47);
x_52 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_48);
return x_52;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
lean_dec(x_3);
x_55 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_53, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_54, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_54);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
lean_dec(x_3);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_64, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_65, x_69);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_65);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_dec(x_72);
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 8:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_75, x_4);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_76, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_77, x_85);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_77);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_dec(x_76);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_78, 0);
lean_dec(x_92);
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_79);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 10:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_95, x_4);
return x_96;
}
case 11:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
lean_dec(x_3);
x_98 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_97, x_4);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
x_99 = 0;
x_100 = lean_box(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_4);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_2, x_3, x_16);
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = lean_name_eq(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_5, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_4, x_5);
x_14 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(x_1, x_2, x_3, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_11);
return x_31;
}
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_5, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_30; 
x_13 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
size_t x_50; size_t x_51; 
x_50 = 1;
x_51 = lean_usize_add(x_5, x_50);
x_5 = x_51;
goto _start;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_dec(x_13);
x_324 = l_Lean_LocalDecl_fvarId(x_53);
x_325 = lean_ctor_get(x_1, 3);
x_326 = l_Lean_LocalDecl_fvarId(x_325);
x_327 = lean_name_eq(x_324, x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_unsigned_to_nat(0u);
x_329 = lean_nat_dec_lt(x_328, x_3);
if (x_329 == 0)
{
uint8_t x_330; 
lean_dec(x_324);
x_330 = 0;
x_54 = x_330;
goto block_323;
}
else
{
size_t x_331; size_t x_332; uint8_t x_333; 
x_331 = 0;
x_332 = lean_usize_of_nat(x_3);
x_333 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(x_324, x_2, x_331, x_332);
lean_dec(x_324);
x_54 = x_333;
goto block_323;
}
}
else
{
uint8_t x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_324);
lean_dec(x_53);
x_334 = 0;
x_335 = lean_box(x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_11);
x_14 = x_336;
goto block_29;
}
block_323:
{
if (x_54 == 0)
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_53, 3);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_get(x_8, x_11);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
lean_inc(x_60);
lean_ctor_set(x_56, 1, x_60);
lean_ctor_set(x_56, 0, x_61);
x_62 = l_Lean_Expr_hasFVar(x_55);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Expr_hasMVar(x_55);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_56);
lean_dec(x_55);
x_64 = lean_st_ref_take(x_8, x_59);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
lean_ctor_set(x_65, 0, x_60);
x_69 = lean_st_ref_set(x_8, x_65, x_66);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = 0;
x_73 = lean_box(x_72);
lean_ctor_set(x_69, 0, x_73);
x_30 = x_69;
goto block_49;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = 0;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_30 = x_77;
goto block_49;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_ctor_get(x_65, 1);
x_79 = lean_ctor_get(x_65, 2);
x_80 = lean_ctor_get(x_65, 3);
x_81 = lean_ctor_get(x_65, 4);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_65);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_60);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_81);
x_83 = lean_st_ref_set(x_8, x_82, x_66);
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
x_86 = 0;
x_87 = lean_box(x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
x_30 = x_88;
goto block_49;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_60);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_2, x_3, x_55, x_56);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_take(x_8, x_59);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_94, 0);
lean_dec(x_97);
lean_ctor_set(x_94, 0, x_92);
x_98 = lean_st_ref_set(x_8, x_94, x_95);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_91);
x_30 = x_98;
goto block_49;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_101);
x_30 = x_102;
goto block_49;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_94, 1);
x_104 = lean_ctor_get(x_94, 2);
x_105 = lean_ctor_get(x_94, 3);
x_106 = lean_ctor_get(x_94, 4);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_94);
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_92);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_105);
lean_ctor_set(x_107, 4, x_106);
x_108 = lean_st_ref_set(x_8, x_107, x_95);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_91);
lean_ctor_set(x_111, 1, x_109);
x_30 = x_111;
goto block_49;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_60);
x_112 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_2, x_3, x_55, x_56);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_st_ref_take(x_8, x_59);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_117, 0);
lean_dec(x_120);
lean_ctor_set(x_117, 0, x_115);
x_121 = lean_st_ref_set(x_8, x_117, x_118);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_121, 0);
lean_dec(x_123);
lean_ctor_set(x_121, 0, x_114);
x_30 = x_121;
goto block_49;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_114);
lean_ctor_set(x_125, 1, x_124);
x_30 = x_125;
goto block_49;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_117, 1);
x_127 = lean_ctor_get(x_117, 2);
x_128 = lean_ctor_get(x_117, 3);
x_129 = lean_ctor_get(x_117, 4);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_117);
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_115);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set(x_130, 3, x_128);
lean_ctor_set(x_130, 4, x_129);
x_131 = lean_st_ref_set(x_8, x_130, x_118);
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
lean_ctor_set(x_134, 0, x_114);
lean_ctor_set(x_134, 1, x_132);
x_30 = x_134;
goto block_49;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_56, 0);
x_136 = lean_ctor_get(x_56, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_56);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
lean_inc(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_Expr_hasFVar(x_55);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Expr_hasMVar(x_55);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_139);
lean_dec(x_55);
x_142 = lean_st_ref_take(x_8, x_136);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 4);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_137);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set(x_150, 2, x_146);
lean_ctor_set(x_150, 3, x_147);
lean_ctor_set(x_150, 4, x_148);
x_151 = lean_st_ref_set(x_8, x_150, x_144);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = 0;
x_155 = lean_box(x_154);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
x_30 = x_156;
goto block_49;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_137);
x_157 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_2, x_3, x_55, x_139);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_st_ref_take(x_8, x_136);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 4);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_160);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set(x_169, 2, x_165);
lean_ctor_set(x_169, 3, x_166);
lean_ctor_set(x_169, 4, x_167);
x_170 = lean_st_ref_set(x_8, x_169, x_163);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_159);
lean_ctor_set(x_173, 1, x_171);
x_30 = x_173;
goto block_49;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_137);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_2, x_3, x_55, x_139);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_8, x_136);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_8, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_30 = x_190;
goto block_49;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_53, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_53, 4);
lean_inc(x_192);
lean_dec(x_53);
x_193 = lean_st_ref_get(x_8, x_11);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_239; lean_object* x_240; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_253 = lean_ctor_get(x_195, 0);
lean_inc(x_253);
lean_dec(x_195);
x_254 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
lean_ctor_set(x_193, 1, x_253);
lean_ctor_set(x_193, 0, x_254);
x_255 = l_Lean_Expr_hasFVar(x_191);
if (x_255 == 0)
{
uint8_t x_256; 
x_256 = l_Lean_Expr_hasMVar(x_191);
if (x_256 == 0)
{
uint8_t x_257; 
lean_dec(x_191);
x_257 = 0;
x_239 = x_257;
x_240 = x_193;
goto block_252;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_258 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_2, x_3, x_191, x_193);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_unbox(x_259);
lean_dec(x_259);
x_239 = x_261;
x_240 = x_260;
goto block_252;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_262 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_2, x_3, x_191, x_193);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_unbox(x_263);
lean_dec(x_263);
x_239 = x_265;
x_240 = x_264;
goto block_252;
}
block_238:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_st_ref_take(x_8, x_196);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = !lean_is_exclusive(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_201, 0);
lean_dec(x_204);
lean_ctor_set(x_201, 0, x_199);
x_205 = lean_st_ref_set(x_8, x_201, x_202);
if (x_197 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_205, 0);
lean_dec(x_207);
x_208 = 1;
x_209 = lean_box(x_208);
lean_ctor_set(x_205, 0, x_209);
x_14 = x_205;
goto block_29;
}
else
{
lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_205, 1);
lean_inc(x_210);
lean_dec(x_205);
x_211 = 1;
x_212 = lean_box(x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_210);
x_14 = x_213;
goto block_29;
}
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_205);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_205, 0);
lean_dec(x_215);
x_216 = 0;
x_217 = lean_box(x_216);
lean_ctor_set(x_205, 0, x_217);
x_14 = x_205;
goto block_29;
}
else
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_205, 1);
lean_inc(x_218);
lean_dec(x_205);
x_219 = 0;
x_220 = lean_box(x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
x_14 = x_221;
goto block_29;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_201, 1);
x_223 = lean_ctor_get(x_201, 2);
x_224 = lean_ctor_get(x_201, 3);
x_225 = lean_ctor_get(x_201, 4);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_201);
x_226 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_226, 0, x_199);
lean_ctor_set(x_226, 1, x_222);
lean_ctor_set(x_226, 2, x_223);
lean_ctor_set(x_226, 3, x_224);
lean_ctor_set(x_226, 4, x_225);
x_227 = lean_st_ref_set(x_8, x_226, x_202);
if (x_197 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
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
x_230 = 1;
x_231 = lean_box(x_230);
if (lean_is_scalar(x_229)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_229;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_228);
x_14 = x_232;
goto block_29;
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_227, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_234 = x_227;
} else {
 lean_dec_ref(x_227);
 x_234 = lean_box(0);
}
x_235 = 0;
x_236 = lean_box(x_235);
if (lean_is_scalar(x_234)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_234;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_233);
x_14 = x_237;
goto block_29;
}
}
}
block_252:
{
if (x_239 == 0)
{
uint8_t x_241; 
x_241 = l_Lean_Expr_hasFVar(x_192);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = l_Lean_Expr_hasMVar(x_192);
if (x_242 == 0)
{
uint8_t x_243; 
lean_dec(x_192);
x_243 = 0;
x_197 = x_243;
x_198 = x_240;
goto block_238;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_2, x_3, x_192, x_240);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unbox(x_245);
lean_dec(x_245);
x_197 = x_247;
x_198 = x_246;
goto block_238;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_248 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_2, x_3, x_192, x_240);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_unbox(x_249);
lean_dec(x_249);
x_197 = x_251;
x_198 = x_250;
goto block_238;
}
}
else
{
lean_dec(x_192);
x_197 = x_239;
x_198 = x_240;
goto block_238;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; uint8_t x_292; lean_object* x_293; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_266 = lean_ctor_get(x_193, 0);
x_267 = lean_ctor_get(x_193, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_193);
x_306 = lean_ctor_get(x_266, 0);
lean_inc(x_306);
lean_dec(x_266);
x_307 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_306);
x_309 = l_Lean_Expr_hasFVar(x_191);
if (x_309 == 0)
{
uint8_t x_310; 
x_310 = l_Lean_Expr_hasMVar(x_191);
if (x_310 == 0)
{
uint8_t x_311; 
lean_dec(x_191);
x_311 = 0;
x_292 = x_311;
x_293 = x_308;
goto block_305;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_312 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_2, x_3, x_191, x_308);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_unbox(x_313);
lean_dec(x_313);
x_292 = x_315;
x_293 = x_314;
goto block_305;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_316 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_2, x_3, x_191, x_308);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_unbox(x_317);
lean_dec(x_317);
x_292 = x_319;
x_293 = x_318;
goto block_305;
}
block_291:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_st_ref_take(x_8, x_267);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 4);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 5, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_270);
lean_ctor_set(x_279, 1, x_274);
lean_ctor_set(x_279, 2, x_275);
lean_ctor_set(x_279, 3, x_276);
lean_ctor_set(x_279, 4, x_277);
x_280 = lean_st_ref_set(x_8, x_279, x_273);
if (x_268 == 0)
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_282 = x_280;
} else {
 lean_dec_ref(x_280);
 x_282 = lean_box(0);
}
x_283 = 1;
x_284 = lean_box(x_283);
if (lean_is_scalar(x_282)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_282;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_281);
x_14 = x_285;
goto block_29;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_280, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_287 = x_280;
} else {
 lean_dec_ref(x_280);
 x_287 = lean_box(0);
}
x_288 = 0;
x_289 = lean_box(x_288);
if (lean_is_scalar(x_287)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_287;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_286);
x_14 = x_290;
goto block_29;
}
}
block_305:
{
if (x_292 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasFVar(x_192);
if (x_294 == 0)
{
uint8_t x_295; 
x_295 = l_Lean_Expr_hasMVar(x_192);
if (x_295 == 0)
{
uint8_t x_296; 
lean_dec(x_192);
x_296 = 0;
x_268 = x_296;
x_269 = x_293;
goto block_291;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_297 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_2, x_3, x_192, x_293);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_unbox(x_298);
lean_dec(x_298);
x_268 = x_300;
x_269 = x_299;
goto block_291;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_2, x_3, x_192, x_293);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_unbox(x_302);
lean_dec(x_302);
x_268 = x_304;
x_269 = x_303;
goto block_291;
}
}
else
{
lean_dec(x_192);
x_268 = x_292;
x_269 = x_293;
goto block_291;
}
}
}
}
}
else
{
uint8_t x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_53);
x_320 = 0;
x_321 = lean_box(x_320);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_11);
x_14 = x_322;
goto block_29;
}
}
}
block_29:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
block_49:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = 1;
x_36 = lean_box(x_35);
lean_ctor_set(x_30, 0, x_36);
x_14 = x_30;
goto block_29;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_14 = x_40;
goto block_29;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 0);
lean_dec(x_42);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_30, 0, x_44);
x_14 = x_30;
goto block_29;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_dec(x_30);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_14 = x_48;
goto block_29;
}
}
}
}
else
{
uint8_t x_337; lean_object* x_338; lean_object* x_339; 
x_337 = 0;
x_338 = lean_box(x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_11);
return x_339;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(x_1, x_2, x_3, x_10, x_17, x_18, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_29 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(x_1, x_2, x_3, x_20, x_27, x_28, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__57(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_5, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_30; 
x_13 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
size_t x_50; size_t x_51; 
x_50 = 1;
x_51 = lean_usize_add(x_5, x_50);
x_5 = x_51;
goto _start;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_53 = lean_ctor_get(x_13, 0);
lean_inc(x_53);
lean_dec(x_13);
x_324 = l_Lean_LocalDecl_fvarId(x_53);
x_325 = lean_ctor_get(x_1, 3);
x_326 = l_Lean_LocalDecl_fvarId(x_325);
x_327 = lean_name_eq(x_324, x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_unsigned_to_nat(0u);
x_329 = lean_nat_dec_lt(x_328, x_3);
if (x_329 == 0)
{
uint8_t x_330; 
lean_dec(x_324);
x_330 = 0;
x_54 = x_330;
goto block_323;
}
else
{
size_t x_331; size_t x_332; uint8_t x_333; 
x_331 = 0;
x_332 = lean_usize_of_nat(x_3);
x_333 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(x_324, x_2, x_331, x_332);
lean_dec(x_324);
x_54 = x_333;
goto block_323;
}
}
else
{
uint8_t x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_324);
lean_dec(x_53);
x_334 = 0;
x_335 = lean_box(x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_11);
x_14 = x_336;
goto block_29;
}
block_323:
{
if (x_54 == 0)
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_53, 3);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_get(x_8, x_11);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
lean_inc(x_60);
lean_ctor_set(x_56, 1, x_60);
lean_ctor_set(x_56, 0, x_61);
x_62 = l_Lean_Expr_hasFVar(x_55);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Expr_hasMVar(x_55);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_56);
lean_dec(x_55);
x_64 = lean_st_ref_take(x_8, x_59);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
lean_ctor_set(x_65, 0, x_60);
x_69 = lean_st_ref_set(x_8, x_65, x_66);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = 0;
x_73 = lean_box(x_72);
lean_ctor_set(x_69, 0, x_73);
x_30 = x_69;
goto block_49;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = 0;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_30 = x_77;
goto block_49;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_ctor_get(x_65, 1);
x_79 = lean_ctor_get(x_65, 2);
x_80 = lean_ctor_get(x_65, 3);
x_81 = lean_ctor_get(x_65, 4);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_65);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_60);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_81);
x_83 = lean_st_ref_set(x_8, x_82, x_66);
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
x_86 = 0;
x_87 = lean_box(x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
x_30 = x_88;
goto block_49;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_60);
x_89 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_2, x_3, x_55, x_56);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_take(x_8, x_59);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_94, 0);
lean_dec(x_97);
lean_ctor_set(x_94, 0, x_92);
x_98 = lean_st_ref_set(x_8, x_94, x_95);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
lean_ctor_set(x_98, 0, x_91);
x_30 = x_98;
goto block_49;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_101);
x_30 = x_102;
goto block_49;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_94, 1);
x_104 = lean_ctor_get(x_94, 2);
x_105 = lean_ctor_get(x_94, 3);
x_106 = lean_ctor_get(x_94, 4);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_94);
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_92);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_105);
lean_ctor_set(x_107, 4, x_106);
x_108 = lean_st_ref_set(x_8, x_107, x_95);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_91);
lean_ctor_set(x_111, 1, x_109);
x_30 = x_111;
goto block_49;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_60);
x_112 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_2, x_3, x_55, x_56);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_st_ref_take(x_8, x_59);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_117, 0);
lean_dec(x_120);
lean_ctor_set(x_117, 0, x_115);
x_121 = lean_st_ref_set(x_8, x_117, x_118);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_121, 0);
lean_dec(x_123);
lean_ctor_set(x_121, 0, x_114);
x_30 = x_121;
goto block_49;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_114);
lean_ctor_set(x_125, 1, x_124);
x_30 = x_125;
goto block_49;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_117, 1);
x_127 = lean_ctor_get(x_117, 2);
x_128 = lean_ctor_get(x_117, 3);
x_129 = lean_ctor_get(x_117, 4);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_117);
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_115);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set(x_130, 3, x_128);
lean_ctor_set(x_130, 4, x_129);
x_131 = lean_st_ref_set(x_8, x_130, x_118);
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
lean_ctor_set(x_134, 0, x_114);
lean_ctor_set(x_134, 1, x_132);
x_30 = x_134;
goto block_49;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_56, 0);
x_136 = lean_ctor_get(x_56, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_56);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
lean_inc(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_Expr_hasFVar(x_55);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Expr_hasMVar(x_55);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_139);
lean_dec(x_55);
x_142 = lean_st_ref_take(x_8, x_136);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 4);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 5, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_137);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set(x_150, 2, x_146);
lean_ctor_set(x_150, 3, x_147);
lean_ctor_set(x_150, 4, x_148);
x_151 = lean_st_ref_set(x_8, x_150, x_144);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = 0;
x_155 = lean_box(x_154);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
x_30 = x_156;
goto block_49;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_137);
x_157 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_2, x_3, x_55, x_139);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_st_ref_take(x_8, x_136);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 4);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_160);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set(x_169, 2, x_165);
lean_ctor_set(x_169, 3, x_166);
lean_ctor_set(x_169, 4, x_167);
x_170 = lean_st_ref_set(x_8, x_169, x_163);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_159);
lean_ctor_set(x_173, 1, x_171);
x_30 = x_173;
goto block_49;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_137);
x_174 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_2, x_3, x_55, x_139);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_take(x_8, x_136);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_179, 4);
lean_inc(x_184);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 x_185 = x_179;
} else {
 lean_dec_ref(x_179);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_181);
lean_ctor_set(x_186, 2, x_182);
lean_ctor_set(x_186, 3, x_183);
lean_ctor_set(x_186, 4, x_184);
x_187 = lean_st_ref_set(x_8, x_186, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_176);
lean_ctor_set(x_190, 1, x_188);
x_30 = x_190;
goto block_49;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_53, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_53, 4);
lean_inc(x_192);
lean_dec(x_53);
x_193 = lean_st_ref_get(x_8, x_11);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_239; lean_object* x_240; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_253 = lean_ctor_get(x_195, 0);
lean_inc(x_253);
lean_dec(x_195);
x_254 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
lean_ctor_set(x_193, 1, x_253);
lean_ctor_set(x_193, 0, x_254);
x_255 = l_Lean_Expr_hasFVar(x_191);
if (x_255 == 0)
{
uint8_t x_256; 
x_256 = l_Lean_Expr_hasMVar(x_191);
if (x_256 == 0)
{
uint8_t x_257; 
lean_dec(x_191);
x_257 = 0;
x_239 = x_257;
x_240 = x_193;
goto block_252;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_258 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_2, x_3, x_191, x_193);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_unbox(x_259);
lean_dec(x_259);
x_239 = x_261;
x_240 = x_260;
goto block_252;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_262 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_2, x_3, x_191, x_193);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_unbox(x_263);
lean_dec(x_263);
x_239 = x_265;
x_240 = x_264;
goto block_252;
}
block_238:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_st_ref_take(x_8, x_196);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = !lean_is_exclusive(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_201, 0);
lean_dec(x_204);
lean_ctor_set(x_201, 0, x_199);
x_205 = lean_st_ref_set(x_8, x_201, x_202);
if (x_197 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_205, 0);
lean_dec(x_207);
x_208 = 1;
x_209 = lean_box(x_208);
lean_ctor_set(x_205, 0, x_209);
x_14 = x_205;
goto block_29;
}
else
{
lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_205, 1);
lean_inc(x_210);
lean_dec(x_205);
x_211 = 1;
x_212 = lean_box(x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_210);
x_14 = x_213;
goto block_29;
}
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_205);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_205, 0);
lean_dec(x_215);
x_216 = 0;
x_217 = lean_box(x_216);
lean_ctor_set(x_205, 0, x_217);
x_14 = x_205;
goto block_29;
}
else
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_205, 1);
lean_inc(x_218);
lean_dec(x_205);
x_219 = 0;
x_220 = lean_box(x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
x_14 = x_221;
goto block_29;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_201, 1);
x_223 = lean_ctor_get(x_201, 2);
x_224 = lean_ctor_get(x_201, 3);
x_225 = lean_ctor_get(x_201, 4);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_201);
x_226 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_226, 0, x_199);
lean_ctor_set(x_226, 1, x_222);
lean_ctor_set(x_226, 2, x_223);
lean_ctor_set(x_226, 3, x_224);
lean_ctor_set(x_226, 4, x_225);
x_227 = lean_st_ref_set(x_8, x_226, x_202);
if (x_197 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
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
x_230 = 1;
x_231 = lean_box(x_230);
if (lean_is_scalar(x_229)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_229;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_228);
x_14 = x_232;
goto block_29;
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_227, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_234 = x_227;
} else {
 lean_dec_ref(x_227);
 x_234 = lean_box(0);
}
x_235 = 0;
x_236 = lean_box(x_235);
if (lean_is_scalar(x_234)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_234;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_233);
x_14 = x_237;
goto block_29;
}
}
}
block_252:
{
if (x_239 == 0)
{
uint8_t x_241; 
x_241 = l_Lean_Expr_hasFVar(x_192);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = l_Lean_Expr_hasMVar(x_192);
if (x_242 == 0)
{
uint8_t x_243; 
lean_dec(x_192);
x_243 = 0;
x_197 = x_243;
x_198 = x_240;
goto block_238;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_2, x_3, x_192, x_240);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unbox(x_245);
lean_dec(x_245);
x_197 = x_247;
x_198 = x_246;
goto block_238;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_248 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_2, x_3, x_192, x_240);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_unbox(x_249);
lean_dec(x_249);
x_197 = x_251;
x_198 = x_250;
goto block_238;
}
}
else
{
lean_dec(x_192);
x_197 = x_239;
x_198 = x_240;
goto block_238;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; uint8_t x_292; lean_object* x_293; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_266 = lean_ctor_get(x_193, 0);
x_267 = lean_ctor_get(x_193, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_193);
x_306 = lean_ctor_get(x_266, 0);
lean_inc(x_306);
lean_dec(x_266);
x_307 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3;
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_306);
x_309 = l_Lean_Expr_hasFVar(x_191);
if (x_309 == 0)
{
uint8_t x_310; 
x_310 = l_Lean_Expr_hasMVar(x_191);
if (x_310 == 0)
{
uint8_t x_311; 
lean_dec(x_191);
x_311 = 0;
x_292 = x_311;
x_293 = x_308;
goto block_305;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_312 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_2, x_3, x_191, x_308);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_unbox(x_313);
lean_dec(x_313);
x_292 = x_315;
x_293 = x_314;
goto block_305;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_316 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_2, x_3, x_191, x_308);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_unbox(x_317);
lean_dec(x_317);
x_292 = x_319;
x_293 = x_318;
goto block_305;
}
block_291:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_st_ref_take(x_8, x_267);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 4);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 5, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_270);
lean_ctor_set(x_279, 1, x_274);
lean_ctor_set(x_279, 2, x_275);
lean_ctor_set(x_279, 3, x_276);
lean_ctor_set(x_279, 4, x_277);
x_280 = lean_st_ref_set(x_8, x_279, x_273);
if (x_268 == 0)
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_282 = x_280;
} else {
 lean_dec_ref(x_280);
 x_282 = lean_box(0);
}
x_283 = 1;
x_284 = lean_box(x_283);
if (lean_is_scalar(x_282)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_282;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_281);
x_14 = x_285;
goto block_29;
}
else
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_280, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_287 = x_280;
} else {
 lean_dec_ref(x_280);
 x_287 = lean_box(0);
}
x_288 = 0;
x_289 = lean_box(x_288);
if (lean_is_scalar(x_287)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_287;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_286);
x_14 = x_290;
goto block_29;
}
}
block_305:
{
if (x_292 == 0)
{
uint8_t x_294; 
x_294 = l_Lean_Expr_hasFVar(x_192);
if (x_294 == 0)
{
uint8_t x_295; 
x_295 = l_Lean_Expr_hasMVar(x_192);
if (x_295 == 0)
{
uint8_t x_296; 
lean_dec(x_192);
x_296 = 0;
x_268 = x_296;
x_269 = x_293;
goto block_291;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_297 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_2, x_3, x_192, x_293);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_unbox(x_298);
lean_dec(x_298);
x_268 = x_300;
x_269 = x_299;
goto block_291;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_2, x_3, x_192, x_293);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_unbox(x_302);
lean_dec(x_302);
x_268 = x_304;
x_269 = x_303;
goto block_291;
}
}
else
{
lean_dec(x_192);
x_268 = x_292;
x_269 = x_293;
goto block_291;
}
}
}
}
}
else
{
uint8_t x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_53);
x_320 = 0;
x_321 = lean_box(x_320);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_11);
x_14 = x_322;
goto block_29;
}
}
}
block_29:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
block_49:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = 1;
x_36 = lean_box(x_35);
lean_ctor_set(x_30, 0, x_36);
x_14 = x_30;
goto block_29;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_14 = x_40;
goto block_29;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 0);
lean_dec(x_42);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_30, 0, x_44);
x_14 = x_30;
goto block_29;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_dec(x_30);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_14 = x_48;
goto block_29;
}
}
}
}
else
{
uint8_t x_337; lean_object* x_338; lean_object* x_339; 
x_337 = 0;
x_338 = lean_box(x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_11);
return x_339;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_18);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_11);
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__57(x_1, x_2, x_3, x_17, x_23, x_24, x_5, x_6, x_7, x_8, x_15);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_array_get_size(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_36 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__57(x_1, x_2, x_3, x_27, x_34, x_35, x_5, x_6, x_7, x_8, x_26);
return x_36;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_11, 0);
lean_dec(x_38);
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_dec(x_11);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__58(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_isFVar(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 6);
x_8 = l_Array_isEmpty___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_37; uint8_t x_38; 
x_9 = lean_array_get_size(x_7);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_9);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_10 = x_39;
goto block_36;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_9);
x_42 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__58(x_7, x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_10 = x_43;
goto block_36;
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
}
block_36:
{
uint8_t x_11; 
lean_dec(x_10);
lean_inc(x_9);
x_11 = l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_7, x_9, x_9, lean_box(0));
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_12, 1);
x_14 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(x_1, x_7, x_9, x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
return x_35;
}
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_47 = 1;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyTR_loop___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__57___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__57(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__58___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__58(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_array_uget(x_1, x_2);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_inc(x_11);
x_20 = l_Lean_Meta_FVarSubst_get(x_19, x_11);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = l_Lean_Meta_saveState___rarg(x_6, x_7, x_8, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_MVarId_clear(x_22, x_21, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_11, x_19);
lean_dec(x_11);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_dec(x_4);
lean_ctor_set(x_23, 1, x_33);
lean_ctor_set(x_23, 0, x_32);
x_12 = x_23;
x_13 = x_29;
goto block_17;
}
else
{
uint8_t x_34; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
x_37 = l_Lean_Exception_isInterrupt(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Exception_isRuntime(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_27);
lean_dec(x_35);
x_39 = l_Lean_Meta_SavedState_restore(x_25, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_25);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_12 = x_4;
x_13 = x_40;
goto block_17;
}
else
{
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
else
{
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = l_Lean_Exception_isInterrupt(x_41);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Exception_isRuntime(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
x_45 = l_Lean_Meta_SavedState_restore(x_25, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_25);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_12 = x_4;
x_13 = x_46;
goto block_17;
}
else
{
lean_object* x_47; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_23, 0);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_51 = l_Lean_MVarId_clear(x_22, x_21, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_dec(x_18);
x_55 = l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_11, x_19);
lean_dec(x_11);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_12 = x_58;
x_13 = x_53;
goto block_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Exception_isInterrupt(x_59);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Exception_isRuntime(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_59);
x_64 = l_Lean_Meta_SavedState_restore(x_49, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_49);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_12 = x_4;
x_13 = x_65;
goto block_17;
}
else
{
lean_object* x_66; 
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
}
else
{
lean_object* x_67; 
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_61;
}
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
x_12 = x_4;
x_13 = x_9;
goto block_17;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_9 = x_13;
goto _start;
}
}
else
{
lean_object* x_68; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_9);
return x_68;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_13, x_15);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_dec(x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_14, x_3, x_12);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_15, x_15);
if (x_21 == 0)
{
size_t x_22; size_t x_23; lean_object* x_24; 
lean_dec(x_15);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_14, x_3, x_12);
x_3 = x_23;
x_4 = x_24;
goto _start;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_15);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(x_1, x_26, x_27, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_33 = lean_array_uset(x_14, x_3, x_29);
x_3 = x_32;
x_4 = x_33;
x_9 = x_30;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(x_8, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_7, x_13);
lean_dec(x_7);
x_15 = lean_array_fget(x_6, x_8);
x_16 = lean_array_get_size(x_2);
x_17 = lean_nat_dec_lt(x_8, x_16);
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 2);
x_21 = lean_nat_add(x_8, x_13);
if (x_17 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
x_22 = l_Lean_instInhabitedName;
x_23 = l_outOfBounds___rarg(x_22);
lean_inc(x_4);
lean_inc(x_23);
x_24 = l_Lean_Expr_const___override(x_23, x_4);
x_25 = l_Lean_mkAppN(x_24, x_5);
x_26 = l_Lean_mkAppN(x_25, x_19);
lean_inc(x_3);
x_27 = l_Lean_Meta_FVarSubst_insert(x_20, x_3, x_26);
lean_ctor_set(x_15, 2, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_array_push(x_10, x_28);
x_7 = x_14;
x_8 = x_21;
x_9 = lean_box(0);
x_10 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_array_fget(x_2, x_8);
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_31);
x_32 = l_Lean_Expr_const___override(x_31, x_4);
x_33 = l_Lean_mkAppN(x_32, x_5);
x_34 = l_Lean_mkAppN(x_33, x_19);
lean_inc(x_3);
x_35 = l_Lean_Meta_FVarSubst_insert(x_20, x_3, x_34);
lean_ctor_set(x_15, 2, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_31);
x_37 = lean_array_push(x_10, x_36);
x_7 = x_14;
x_8 = x_21;
x_9 = lean_box(0);
x_10 = x_37;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
x_41 = lean_ctor_get(x_15, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_42 = lean_nat_add(x_8, x_13);
if (x_17 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
x_43 = l_Lean_instInhabitedName;
x_44 = l_outOfBounds___rarg(x_43);
lean_inc(x_4);
lean_inc(x_44);
x_45 = l_Lean_Expr_const___override(x_44, x_4);
x_46 = l_Lean_mkAppN(x_45, x_5);
x_47 = l_Lean_mkAppN(x_46, x_40);
lean_inc(x_3);
x_48 = l_Lean_Meta_FVarSubst_insert(x_41, x_3, x_47);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
x_51 = lean_array_push(x_10, x_50);
x_7 = x_14;
x_8 = x_42;
x_9 = lean_box(0);
x_10 = x_51;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_array_fget(x_2, x_8);
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_53);
x_54 = l_Lean_Expr_const___override(x_53, x_4);
x_55 = l_Lean_mkAppN(x_54, x_5);
x_56 = l_Lean_mkAppN(x_55, x_40);
lean_inc(x_3);
x_57 = l_Lean_Meta_FVarSubst_insert(x_41, x_3, x_56);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_39);
lean_ctor_set(x_58, 1, x_40);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
x_60 = lean_array_push(x_10, x_59);
x_7 = x_14;
x_8 = x_42;
x_9 = lean_box(0);
x_10 = x_60;
goto _start;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_mapFinIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_1, x_6, x_8, lean_box(0), x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__6;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_1, x_10);
x_12 = lean_ctor_get(x_7, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_12, x_13);
if (x_11 == 0)
{
if (x_15 == 0)
{
uint8_t x_99; 
lean_dec(x_14);
x_99 = 0;
x_16 = x_99;
goto block_98;
}
else
{
lean_object* x_100; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1(x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_100;
}
}
else
{
if (x_15 == 0)
{
uint8_t x_101; 
lean_dec(x_14);
x_101 = 1;
x_16 = x_101;
goto block_98;
}
else
{
lean_object* x_102; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1(x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_102;
}
}
block_98:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_12, x_17);
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_7, 3);
lean_dec(x_21);
lean_ctor_set(x_7, 3, x_18);
x_22 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Meta_intro1Core(x_2, x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_Meta_Cases_unifyEqs_x3f___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Meta_unifyEq_x3f(x_27, x_26, x_3, x_28, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_nat_sub(x_1, x_17);
lean_dec(x_1);
x_43 = lean_nat_add(x_42, x_41);
lean_dec(x_41);
lean_dec(x_42);
x_1 = x_43;
x_2 = x_39;
x_3 = x_40;
x_9 = x_38;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
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
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
return x_23;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
x_55 = lean_ctor_get(x_7, 2);
x_56 = lean_ctor_get(x_7, 5);
x_57 = lean_ctor_get(x_7, 6);
x_58 = lean_ctor_get(x_7, 7);
x_59 = lean_ctor_get(x_7, 8);
x_60 = lean_ctor_get(x_7, 9);
x_61 = lean_ctor_get(x_7, 10);
x_62 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_63 = lean_ctor_get(x_7, 11);
x_64 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
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
lean_dec(x_7);
x_65 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_54);
lean_ctor_set(x_65, 2, x_55);
lean_ctor_set(x_65, 3, x_18);
lean_ctor_set(x_65, 4, x_13);
lean_ctor_set(x_65, 5, x_56);
lean_ctor_set(x_65, 6, x_57);
lean_ctor_set(x_65, 7, x_58);
lean_ctor_set(x_65, 8, x_59);
lean_ctor_set(x_65, 9, x_60);
lean_ctor_set(x_65, 10, x_61);
lean_ctor_set(x_65, 11, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*12, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*12 + 1, x_64);
x_66 = 0;
lean_inc(x_8);
lean_inc(x_65);
lean_inc(x_6);
lean_inc(x_5);
x_67 = l_Lean_Meta_intro1Core(x_2, x_66, x_5, x_6, x_65, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l_Lean_Meta_Cases_unifyEqs_x3f___closed__1;
lean_inc(x_8);
lean_inc(x_65);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_73 = l_Lean_Meta_unifyEq_x3f(x_71, x_70, x_3, x_72, x_4, x_5, x_6, x_65, x_8, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 2);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_nat_sub(x_1, x_17);
lean_dec(x_1);
x_85 = lean_nat_add(x_84, x_83);
lean_dec(x_83);
lean_dec(x_84);
x_1 = x_85;
x_2 = x_81;
x_3 = x_82;
x_7 = x_65;
x_9 = x_80;
goto _start;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = lean_ctor_get(x_73, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_89 = x_73;
} else {
 lean_dec_ref(x_73);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = lean_ctor_get(x_67, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_67, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_93 = x_67;
} else {
 lean_dec_ref(x_67);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_3);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_9);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_inc(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_14);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_10 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_array_size(x_29);
x_31 = 0;
lean_inc(x_28);
x_32 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(x_28, x_30, x_31, x_29);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_12, 0, x_33);
x_34 = lean_array_push(x_5, x_12);
x_35 = 1;
x_36 = lean_usize_add(x_3, x_35);
x_3 = x_36;
x_5 = x_34;
x_10 = x_26;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
lean_inc(x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_47 = l_Lean_Meta_Cases_unifyEqs_x3f(x_1, x_44, x_45, x_46, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; size_t x_50; size_t x_51; 
lean_dec(x_43);
lean_dec(x_42);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = 1;
x_51 = lean_usize_add(x_3, x_50);
x_3 = x_51;
x_10 = x_49;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_dec(x_42);
x_58 = lean_array_size(x_57);
x_59 = 0;
lean_inc(x_56);
x_60 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(x_56, x_58, x_59, x_57);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_43);
x_63 = lean_array_push(x_5, x_62);
x_64 = 1;
x_65 = lean_usize_add(x_3, x_64);
x_3 = x_65;
x_5 = x_63;
x_10 = x_54;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_69 = x_47;
} else {
 lean_dec_ref(x_47);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_5);
lean_ctor_set(x_71, 1, x_10);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2(x_1, x_2, x_16, x_17, x_18, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_array_mk(x_14);
lean_inc(x_3);
x_16 = l_Lean_MVarId_induction(x_2, x_3, x_7, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_18, x_15, x_3, x_5, x_6);
lean_dec(x_15);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_20, x_15, x_3, x_5, x_6);
lean_dec(x_15);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesAuxOn", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
x_15 = l_Lean_Meta_getInductiveUniverseAndParams(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_casesOnSuffix;
lean_inc(x_22);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_st_ref_get(x_10, x_17);
if (x_6 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(x_20, x_3, x_4, x_5, x_18, x_19, x_24, x_27, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__2;
x_33 = lean_name_eq(x_22, x_32);
lean_dec(x_22);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(x_20, x_3, x_4, x_5, x_18, x_19, x_24, x_34, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_19);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__4;
x_37 = l_Lean_Environment_contains(x_31, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(x_20, x_3, x_4, x_5, x_18, x_19, x_24, x_38, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_19);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
x_40 = lean_box(0);
x_41 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(x_20, x_3, x_4, x_5, x_18, x_19, x_36, x_40, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_19);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_12);
if (x_46 == 0)
{
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_11 = l_Lean_Expr_fvar___override(x_2);
x_12 = lean_box(x_5);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___boxed), 11, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_12);
x_14 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_10, x_11, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_1, x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(x_19, x_17, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not applicable to the given hypothesis", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__5;
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__6;
x_3 = l_Lean_Meta_Cases_cases___lambda__2___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after generalizeIndices\n", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(x_3, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Cases_cases___lambda__2___closed__4;
x_17 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_16, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Cases_cases___lambda__2___closed__8;
x_29 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_28, x_6, x_7, x_8, x_9, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_14);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Cases_cases___lambda__1(x_26, x_4, x_20, x_33, x_6, x_7, x_8, x_9, x_32);
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
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_ctor_set(x_14, 0, x_38);
x_39 = l_Lean_Meta_Cases_cases___lambda__2___closed__10;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 0, x_39);
x_40 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_28, x_41, x_6, x_7, x_8, x_9, x_36);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_Cases_cases___lambda__1(x_26, x_4, x_20, x_43, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_ctor_get(x_26, 0);
lean_inc(x_47);
lean_ctor_set(x_14, 0, x_47);
x_48 = l_Lean_Meta_Cases_cases___lambda__2___closed__10;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_14);
x_50 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_28, x_51, x_6, x_7, x_8, x_9, x_46);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Meta_Cases_cases___lambda__1(x_26, x_4, x_20, x_53, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_free_object(x_14);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_25, 0);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_25);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_free_object(x_14);
x_60 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_3, x_4, x_20, x_5, x_6, x_7, x_8, x_9, x_18);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_14, 0);
lean_inc(x_61);
lean_dec(x_14);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 2);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_eq(x_63, x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_66 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_Cases_cases___lambda__2___closed__8;
x_70 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_69, x_6, x_7, x_8, x_9, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_box(0);
x_75 = l_Lean_Meta_Cases_cases___lambda__1(x_67, x_4, x_61, x_74, x_6, x_7, x_8, x_9, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Lean_Meta_Cases_cases___lambda__2___closed__10;
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_77;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_69, x_83, x_6, x_7, x_8, x_9, x_76);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_Cases_cases___lambda__1(x_67, x_4, x_61, x_85, x_6, x_7, x_8, x_9, x_86);
lean_dec(x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_88 = lean_ctor_get(x_66, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_90 = x_66;
} else {
 lean_dec_ref(x_66);
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
else
{
lean_object* x_92; 
x_92 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_3, x_4, x_61, x_5, x_6, x_7, x_8, x_9, x_18);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_13);
if (x_93 == 0)
{
return x_13;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_13, 0);
x_95 = lean_ctor_get(x_13, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_13);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_11);
if (x_97 == 0)
{
return x_11;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_11, 0);
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_11);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_Cases_cases___closed__1;
x_11 = lean_box(x_4);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__2___boxed), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Exception_isInterrupt(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Exception_isRuntime(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_13);
x_19 = l_Lean_Meta_throwNestedTacticEx___rarg(x_10, x_15, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lean_Exception_isInterrupt(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isRuntime(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Meta_throwNestedTacticEx___rarg(x_10, x_20, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Cases_cases___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_Cases_cases___lambda__2(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_MVarId_cases(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_MVarId_casesRec___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_MVarId_casesRec___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
lean_dec(x_19);
x_23 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = l_Lean_Exception_isInterrupt(x_30);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
x_34 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_10, x_9);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_uget(x_8, x_10);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_21);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4(x_1, x_2, x_3, x_4, x_19, x_21, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_11, 0, x_27);
lean_ctor_set(x_23, 0, x_11);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_11, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
lean_dec(x_21);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
lean_inc(x_7);
lean_ctor_set(x_11, 1, x_32);
lean_ctor_set(x_11, 0, x_7);
x_33 = 1;
x_34 = lean_usize_add(x_10, x_33);
x_10 = x_34;
x_16 = x_31;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_11);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
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
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_dec(x_11);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_40);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4(x_1, x_2, x_3, x_4, x_19, x_40, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
lean_dec(x_40);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_10, x_51);
x_10 = x_52;
x_11 = x_50;
x_16 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_array_to_list(x_13);
x_15 = l_List_mapTR_loop___at_Lean_MVarId_casesRec___spec__1(x_14, x_4);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_array_to_list(x_16);
x_19 = l_List_mapTR_loop___at_Lean_MVarId_casesRec___spec__1(x_18, x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_uget(x_7, x_9);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_32; 
lean_inc(x_19);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_19);
x_21 = x_32;
x_22 = x_15;
goto block_31;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_34);
x_35 = lean_apply_6(x_1, x_34, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_18);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_3);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_21 = x_39;
x_22 = x_38;
goto block_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_LocalDecl_fvarId(x_34);
lean_dec(x_34);
x_42 = lean_box(0);
x_43 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_2);
x_44 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___lambda__1), 9, 4);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_41);
lean_closure_set(x_44, 2, x_43);
lean_closure_set(x_44, 3, x_42);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_45 = l_Lean_observing_x3f___at_Lean_MVarId_casesRec___spec__2(x_44, x_11, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_18);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_3);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_3);
x_21 = x_48;
x_22 = x_47;
goto block_31;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
lean_inc(x_46);
lean_ctor_set(x_18, 0, x_46);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_18);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_tag(x_46, 0);
lean_ctor_set(x_46, 0, x_53);
x_21 = x_46;
x_22 = x_49;
goto block_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_18);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_21 = x_56;
x_22 = x_49;
goto block_31;
}
}
}
else
{
uint8_t x_57; 
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
return x_45;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_18);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_35);
if (x_61 == 0)
{
return x_35;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_35, 0);
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_35);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_18, 0);
lean_inc(x_65);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_65);
x_66 = lean_apply_6(x_1, x_65, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
lean_inc(x_3);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_3);
x_21 = x_70;
x_22 = x_69;
goto block_31;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = l_Lean_LocalDecl_fvarId(x_65);
lean_dec(x_65);
x_73 = lean_box(0);
x_74 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_2);
x_75 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___lambda__1), 9, 4);
lean_closure_set(x_75, 0, x_2);
lean_closure_set(x_75, 1, x_72);
lean_closure_set(x_75, 2, x_74);
lean_closure_set(x_75, 3, x_73);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_76 = l_Lean_observing_x3f___at_Lean_MVarId_casesRec___spec__2(x_75, x_11, x_12, x_13, x_14, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_3);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_3);
x_21 = x_79;
x_22 = x_78;
goto block_31;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
lean_inc(x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_77);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_82 = x_77;
} else {
 lean_dec_ref(x_77);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_82;
 lean_ctor_set_tag(x_85, 0);
}
lean_ctor_set(x_85, 0, x_84);
x_21 = x_85;
x_22 = x_80;
goto block_31;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_65);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_66, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_92 = x_66;
} else {
 lean_dec_ref(x_66);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
block_31:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
if (lean_is_scalar(x_20)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_20;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
lean_inc(x_6);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_9, x_28);
x_9 = x_29;
x_10 = x_27;
x_15 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
x_16 = lean_array_size(x_12);
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__5(x_1, x_2, x_3, x_4, x_12, x_13, x_14, x_12, x_16, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
x_39 = lean_array_size(x_35);
x_40 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6(x_1, x_2, x_3, x_35, x_36, x_37, x_35, x_39, x_40, x_38, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_box(0);
x_47 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___lambda__1(x_45, x_46, x_7, x_8, x_9, x_10, x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_41, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_50);
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_uget(x_7, x_9);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_36; 
lean_inc(x_19);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_19);
x_21 = x_36;
x_22 = x_15;
goto block_35;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_38);
x_39 = lean_apply_6(x_1, x_38, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_18);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_inc(x_3);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_3);
x_21 = x_43;
x_22 = x_42;
goto block_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_LocalDecl_fvarId(x_38);
lean_dec(x_38);
x_46 = lean_box(0);
x_47 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_2);
x_48 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___lambda__1), 9, 4);
lean_closure_set(x_48, 0, x_2);
lean_closure_set(x_48, 1, x_45);
lean_closure_set(x_48, 2, x_47);
lean_closure_set(x_48, 3, x_46);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_49 = l_Lean_observing_x3f___at_Lean_MVarId_casesRec___spec__2(x_48, x_11, x_12, x_13, x_14, x_44);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_18);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_3);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_3);
x_21 = x_52;
x_22 = x_51;
goto block_35;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
lean_inc(x_50);
lean_ctor_set(x_18, 0, x_50);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
lean_dec(x_55);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_57);
x_21 = x_50;
x_22 = x_53;
goto block_35;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_18);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_21 = x_60;
x_22 = x_53;
goto block_35;
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
return x_49;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_49, 0);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_49);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_18);
lean_dec(x_38);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_39);
if (x_65 == 0)
{
return x_39;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_39, 0);
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_39);
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
x_69 = lean_ctor_get(x_18, 0);
lean_inc(x_69);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_69);
x_70 = lean_apply_6(x_1, x_69, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
lean_inc(x_3);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_3);
x_21 = x_74;
x_22 = x_73;
goto block_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = l_Lean_LocalDecl_fvarId(x_69);
lean_dec(x_69);
x_77 = lean_box(0);
x_78 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_2);
x_79 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___lambda__1), 9, 4);
lean_closure_set(x_79, 0, x_2);
lean_closure_set(x_79, 1, x_76);
lean_closure_set(x_79, 2, x_78);
lean_closure_set(x_79, 3, x_77);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_80 = l_Lean_observing_x3f___at_Lean_MVarId_casesRec___spec__2(x_79, x_11, x_12, x_13, x_14, x_75);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_3);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_3);
x_21 = x_83;
x_22 = x_82;
goto block_35;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
lean_inc(x_81);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_81);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 1, 0);
} else {
 x_89 = x_86;
 lean_ctor_set_tag(x_89, 0);
}
lean_ctor_set(x_89, 0, x_88);
x_21 = x_89;
x_22 = x_84;
goto block_35;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_80, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_92 = x_80;
} else {
 lean_dec_ref(x_80);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_69);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_70, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_96 = x_70;
} else {
 lean_dec_ref(x_70);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
block_35:
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_ctor_set_tag(x_21, 1);
if (lean_is_scalar(x_20)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_20;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
if (lean_is_scalar(x_20)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_20;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
lean_inc(x_6);
if (lean_is_scalar(x_20)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_20;
}
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_30);
x_32 = 1;
x_33 = lean_usize_add(x_9, x_32);
x_9 = x_33;
x_10 = x_31;
x_15 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_array_size(x_22);
x_27 = 0;
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__7(x_1, x_2, x_3, x_22, x_23, x_24, x_22, x_26, x_27, x_25, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_12);
if (x_47 == 0)
{
return x_12;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_12, 0);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_12);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_casesRec___lambda__1___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MVarId_casesRec___lambda__1___closed__1;
x_12 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3(x_1, x_2, x_11, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_casesRec___lambda__2), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_saturate(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_18, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_casesRec___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_casesRec___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_casesRec___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_casesAnd___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_LocalDecl_type(x_1);
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_MVarId_casesAnd___lambda__1___closed__2;
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Expr_isAppOfArity(x_10, x_11, x_12);
lean_dec(x_10);
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = l_Lean_MVarId_casesAnd___lambda__1___closed__2;
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
lean_dec(x_15);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_casesAnd___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected number of goals", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_casesAnd___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_casesAnd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_casesAnd___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_MVarId_casesAnd___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_MVarId_casesRec(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MVarId_casesAnd___closed__4;
x_12 = l_Lean_Meta_exactlyOne(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_casesAnd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_casesAnd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_LocalDecl_type(x_1);
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isEq(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_isHEq(x_10);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = l_Lean_Expr_isEq(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Expr_isHEq(x_16);
lean_dec(x_16);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_substEqs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_substEqs___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_MVarId_substEqs___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_MVarId_casesRec(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MVarId_casesAnd___closed__4;
x_12 = l_Lean_Meta_ensureAtMostOne(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_substEqs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_substEqs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'byCases' tactic failed, unexpected new hypothesis", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_fget(x_8, x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
x_20 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__2;
x_21 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___spec__1(x_20, x_2, x_3, x_4, x_5, x_6);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_byCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_MVarId_byCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hByCases", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byCases___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'byCases' tactic failed, unexpected number of subgoals", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCases___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_byCases___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_9 = l_Lean_mkNot(x_2);
lean_inc(x_2);
x_10 = l_Lean_mkOr(x_2, x_9);
x_11 = l_Lean_mkEM(x_2);
x_12 = l_Lean_MVarId_byCases___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_MVarId_assert(x_1, x_12, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_intro1Core(x_14, x_16, x_4, x_5, x_6, x_7, x_15);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_16);
lean_inc(x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Meta_Cases_cases(x_22, x_21, x_28, x_16, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_get_size(x_30);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_free_object(x_18);
x_35 = l_Lean_MVarId_byCases___closed__4;
x_36 = l_Lean_throwError___at_Lean_MVarId_byCases___spec__1(x_35, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_fget(x_30, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_array_fget(x_30, x_39);
lean_dec(x_30);
x_41 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_38, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_40, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_40);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set(x_18, 1, x_46);
lean_ctor_set(x_18, 0, x_42);
lean_ctor_set(x_44, 0, x_18);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_18, 1, x_47);
lean_ctor_set(x_18, 0, x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_42);
lean_free_object(x_18);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
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
lean_dec(x_40);
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_29);
if (x_58 == 0)
{
return x_29;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_29, 0);
x_60 = lean_ctor_get(x_29, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_29);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_16);
lean_inc(x_66);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_array_mk(x_68);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Lean_Meta_Cases_cases(x_63, x_62, x_69, x_16, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_array_get_size(x_71);
x_74 = lean_unsigned_to_nat(2u);
x_75 = lean_nat_dec_eq(x_73, x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_71);
x_76 = l_Lean_MVarId_byCases___closed__4;
x_77 = l_Lean_throwError___at_Lean_MVarId_byCases___spec__1(x_76, x_4, x_5, x_6, x_7, x_72);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_array_fget(x_71, x_78);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_array_fget(x_71, x_80);
lean_dec(x_71);
x_82 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_79, x_4, x_5, x_6, x_7, x_72);
lean_dec(x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_81, x_4, x_5, x_6, x_7, x_84);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_81);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_86);
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_83);
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_93 = x_85;
} else {
 lean_dec_ref(x_85);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_81);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_97 = x_82;
} else {
 lean_dec_ref(x_82);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_99 = lean_ctor_get(x_70, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_70, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_101 = x_70;
} else {
 lean_dec_ref(x_70);
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
uint8_t x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_17);
if (x_103 == 0)
{
return x_17;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_17, 0);
x_105 = lean_ctor_get(x_17, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_17);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_13);
if (x_107 == 0)
{
return x_13;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_13, 0);
x_109 = lean_ctor_get(x_13, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_13);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_byCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_MVarId_byCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byCasesDec___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_byCasesDec___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'byCasesDec' tactic failed, unexpected number of subgoals", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_byCasesDec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_byCasesDec___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byCasesDec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = l_Lean_MVarId_byCasesDec___closed__3;
x_12 = l_Lean_Expr_app___override(x_11, x_2);
x_13 = l_Lean_MVarId_byCases___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_MVarId_assert(x_1, x_13, x_12, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_intro1Core(x_15, x_17, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_10);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_17);
lean_inc(x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Meta_Cases_cases(x_23, x_22, x_28, x_17, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_get_size(x_30);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_free_object(x_19);
x_35 = l_Lean_MVarId_byCasesDec___closed__5;
x_36 = l_Lean_throwError___at_Lean_MVarId_byCases___spec__1(x_35, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_fget(x_30, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_array_fget(x_30, x_39);
lean_dec(x_30);
x_41 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_40, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_38, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_38);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set(x_19, 1, x_46);
lean_ctor_set(x_19, 0, x_42);
lean_ctor_set(x_44, 0, x_19);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_19, 1, x_47);
lean_ctor_set(x_19, 0, x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_42);
lean_free_object(x_19);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
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
lean_dec(x_38);
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_29);
if (x_58 == 0)
{
return x_29;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_29, 0);
x_60 = lean_ctor_get(x_29, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_29);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_10);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_17);
lean_inc(x_65);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_mk(x_67);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_69 = l_Lean_Meta_Cases_cases(x_63, x_62, x_68, x_17, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_array_get_size(x_70);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_nat_dec_eq(x_72, x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
x_75 = l_Lean_MVarId_byCasesDec___closed__5;
x_76 = l_Lean_throwError___at_Lean_MVarId_byCases___spec__1(x_75, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_array_fget(x_70, x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_array_fget(x_70, x_79);
lean_dec(x_70);
x_81 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_80, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal(x_78, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_78);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_96 = x_81;
} else {
 lean_dec_ref(x_81);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_98 = lean_ctor_get(x_69, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_69, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_100 = x_69;
} else {
 lean_dec_ref(x_69);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = !lean_is_exclusive(x_18);
if (x_102 == 0)
{
return x_18;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_18, 0);
x_104 = lean_ctor_get(x_18, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_18);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_106 = !lean_is_exclusive(x_14);
if (x_106 == 0)
{
return x_14;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_14, 0);
x_108 = lean_ctor_get(x_14, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_14);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__2;
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__8;
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__9;
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__10;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__12;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__14;
x_2 = lean_unsigned_to_nat(3794u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__8;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Acyclic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_UnifyEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__3);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4);
l_Lean_Meta_getInductiveUniverseAndParams___closed__1 = _init_l_Lean_Meta_getInductiveUniverseAndParams___closed__1();
lean_mark_persistent(l_Lean_Meta_getInductiveUniverseAndParams___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1);
l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__1 = _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__1);
l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2 = _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2);
l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__3 = _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__3);
l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4 = _init_l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4);
l_Lean_Meta_generalizeTargetsEq___closed__1 = _init_l_Lean_Meta_generalizeTargetsEq___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___closed__1);
l_Lean_Meta_generalizeTargetsEq___closed__2 = _init_l_Lean_Meta_generalizeTargetsEq___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeTargetsEq___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__7 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__7);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__8 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__8);
l_Lean_Meta_generalizeIndices___lambda__1___closed__1 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__1);
l_Lean_Meta_generalizeIndices___lambda__1___closed__2 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1);
l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__1 = _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__1);
l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__2 = _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__2();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__2);
l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3 = _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_Cases_unifyEqs_x3f___spec__1___closed__6);
l_Lean_Meta_Cases_unifyEqs_x3f___closed__1 = _init_l_Lean_Meta_Cases_unifyEqs_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs_x3f___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__2___closed__4);
l_Lean_Meta_Cases_cases___lambda__2___closed__1 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__1);
l_Lean_Meta_Cases_cases___lambda__2___closed__2 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__2);
l_Lean_Meta_Cases_cases___lambda__2___closed__3 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__3);
l_Lean_Meta_Cases_cases___lambda__2___closed__4 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__4);
l_Lean_Meta_Cases_cases___lambda__2___closed__5 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__5);
l_Lean_Meta_Cases_cases___lambda__2___closed__6 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__6);
l_Lean_Meta_Cases_cases___lambda__2___closed__7 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__7);
l_Lean_Meta_Cases_cases___lambda__2___closed__8 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__8);
l_Lean_Meta_Cases_cases___lambda__2___closed__9 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__9);
l_Lean_Meta_Cases_cases___lambda__2___closed__10 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__10);
l_Lean_Meta_Cases_cases___closed__1 = _init_l_Lean_Meta_Cases_cases___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___closed__1);
l_Lean_MVarId_casesRec___lambda__1___closed__1 = _init_l_Lean_MVarId_casesRec___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_casesRec___lambda__1___closed__1);
l_Lean_MVarId_casesAnd___lambda__1___closed__1 = _init_l_Lean_MVarId_casesAnd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_casesAnd___lambda__1___closed__1);
l_Lean_MVarId_casesAnd___lambda__1___closed__2 = _init_l_Lean_MVarId_casesAnd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_casesAnd___lambda__1___closed__2);
l_Lean_MVarId_casesAnd___closed__1 = _init_l_Lean_MVarId_casesAnd___closed__1();
lean_mark_persistent(l_Lean_MVarId_casesAnd___closed__1);
l_Lean_MVarId_casesAnd___closed__2 = _init_l_Lean_MVarId_casesAnd___closed__2();
lean_mark_persistent(l_Lean_MVarId_casesAnd___closed__2);
l_Lean_MVarId_casesAnd___closed__3 = _init_l_Lean_MVarId_casesAnd___closed__3();
lean_mark_persistent(l_Lean_MVarId_casesAnd___closed__3);
l_Lean_MVarId_casesAnd___closed__4 = _init_l_Lean_MVarId_casesAnd___closed__4();
lean_mark_persistent(l_Lean_MVarId_casesAnd___closed__4);
l_Lean_MVarId_substEqs___closed__1 = _init_l_Lean_MVarId_substEqs___closed__1();
lean_mark_persistent(l_Lean_MVarId_substEqs___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_toByCasesSubgoal___closed__2);
l_Lean_MVarId_byCases___closed__1 = _init_l_Lean_MVarId_byCases___closed__1();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__1);
l_Lean_MVarId_byCases___closed__2 = _init_l_Lean_MVarId_byCases___closed__2();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__2);
l_Lean_MVarId_byCases___closed__3 = _init_l_Lean_MVarId_byCases___closed__3();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__3);
l_Lean_MVarId_byCases___closed__4 = _init_l_Lean_MVarId_byCases___closed__4();
lean_mark_persistent(l_Lean_MVarId_byCases___closed__4);
l_Lean_MVarId_byCasesDec___closed__1 = _init_l_Lean_MVarId_byCasesDec___closed__1();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__1);
l_Lean_MVarId_byCasesDec___closed__2 = _init_l_Lean_MVarId_byCasesDec___closed__2();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__2);
l_Lean_MVarId_byCasesDec___closed__3 = _init_l_Lean_MVarId_byCasesDec___closed__3();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__3);
l_Lean_MVarId_byCasesDec___closed__4 = _init_l_Lean_MVarId_byCasesDec___closed__4();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__4);
l_Lean_MVarId_byCasesDec___closed__5 = _init_l_Lean_MVarId_byCasesDec___closed__5();
lean_mark_persistent(l_Lean_MVarId_byCasesDec___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794____closed__15);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3794_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
