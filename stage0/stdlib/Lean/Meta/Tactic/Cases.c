// Lean compiler output
// Module: Lean.Meta.Tactic.Cases
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Injection Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Subst
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___closed__1;
static lean_object* l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_byCases_toByCasesSubgoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__3;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1;
lean_object* l_Lean_MetavarContext_getExprAssignment_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__10;
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesAnd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4;
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__9;
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__8;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_byCases_toByCasesSubgoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_byCases_toByCasesSubgoal___closed__1;
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_byCases___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_byCases___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_byCases___closed__2;
static lean_object* l_Lean_Meta_byCases___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_casesAnd___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases_toByCasesSubgoal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_casesAnd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__11;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_byCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___closed__1;
static lean_object* l_Lean_Meta_casesAnd___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_casesAnd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1___at_Lean_Meta_Cases_unifyEqs_substEq___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getInductiveUniverseAndParams___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substEqs___closed__1;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_unifyEqs_substEq___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__6;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkEM(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_casesRec___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1___at_Lean_Meta_Cases_unifyEqs_substEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_casesRec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3624_(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Cases_unifyEqs_substEq___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_substEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_byCases_toByCasesSubgoal___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_nminors___default___boxed(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_nminors___default(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_heqToEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2___at_Lean_Meta_casesRec___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_casesRec___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_casesRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_heqToEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substEqs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases_toByCasesSubgoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_byCases___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstructorApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__3;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_unifyEqs_injection___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Meta_substEqs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__1;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__7;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2;
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_casesAnd___closed__2;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__5;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_casesAnd___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Cases_unifyEqs_injection___closed__1;
static lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__2;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_casesAnd___closed__1;
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
x_1 = lean_mk_string("failed to compile pattern matching, inductive type expected");
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
x_1 = lean_mk_string("");
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
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
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
x_2 = l_Lean_mkSort(x_1);
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
x_18 = lean_environment_find(x_17, x_11);
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
x_23 = l_Lean_Expr_getAppNumArgsAux(x_8, x_22);
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
x_36 = lean_environment_find(x_35, x_11);
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
x_41 = l_Lean_Expr_getAppNumArgsAux(x_8, x_40);
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
x_1 = lean_mk_string("HEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
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
x_25 = l_Lean_mkConst(x_24, x_23);
lean_inc(x_1);
lean_inc(x_9);
x_26 = l_Lean_mkApp4(x_25, x_9, x_1, x_12, x_2);
x_27 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
x_28 = l_Lean_mkConst(x_27, x_23);
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
x_35 = l_Lean_mkConst(x_34, x_33);
lean_inc(x_1);
lean_inc(x_9);
x_36 = l_Lean_mkApp4(x_35, x_9, x_1, x_12, x_2);
x_37 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__4;
x_38 = l_Lean_mkConst(x_37, x_33);
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
x_47 = l_Lean_mkConst(x_46, x_45);
lean_inc(x_1);
lean_inc(x_9);
x_48 = l_Lean_mkApp3(x_47, x_9, x_1, x_2);
x_49 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7;
x_50 = l_Lean_mkConst(x_49, x_45);
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
x_57 = l_Lean_mkConst(x_56, x_55);
lean_inc(x_1);
lean_inc(x_9);
x_58 = l_Lean_mkApp3(x_57, x_9, x_1, x_2);
x_59 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__7;
x_60 = l_Lean_mkConst(x_59, x_55);
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
lean_dec(x_1);
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
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_1, x_4);
x_17 = lean_array_get(x_15, x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(x_16, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___lambda__1), 13, 7);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_6);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_1);
lean_closure_set(x_23, 5, x_2);
lean_closure_set(x_23, 6, x_3);
x_24 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs_loop___rarg___closed__2;
x_25 = 0;
x_26 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__2___rarg(x_24, x_25, x_21, x_23, x_7, x_8, x_9, x_10, x_20);
return x_26;
}
else
{
uint8_t x_27; 
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
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
x_10 = l_Lean_Meta_getMVarType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = 1;
lean_inc(x_5);
x_15 = l_Lean_Meta_mkForallFVars(x_3, x_11, x_13, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_mkForallFVars(x_2, x_16, x_13, x_14, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
x_1 = lean_mk_string("invalid number of targets #");
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
x_1 = lean_mk_string(", motive expects #");
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
lean_dec(x_4);
x_10 = lean_array_get_size(x_3);
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Nat_repr(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_generalizeTargetsEq___lambda__3___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Nat_repr(x_10);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_25, x_5, x_6, x_7, x_8, x_9);
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
lean_inc(x_6);
lean_inc(x_1);
x_10 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeTargetsEq___lambda__3), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_4, x_12, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_Meta_getMVarTag(x_1, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_5);
x_21 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_16, x_19, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_mkAppN(x_22, x_3);
x_25 = l_Lean_mkAppN(x_24, x_17);
x_26 = l_Lean_Meta_assignExprMVar(x_1, x_25, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
uint8_t x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("generalizeTargets");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeTargetsEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_generalizeTargetsEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
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
x_11 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_1, x_10);
lean_inc(x_2);
x_17 = l_Lean_Meta_getMVarType(x_2, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_2);
x_20 = l_Lean_Meta_getMVarTag(x_2, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
x_24 = 1;
lean_inc(x_11);
lean_inc(x_16);
x_25 = l_Lean_Meta_mkForallFVars(x_16, x_18, x_23, x_24, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___closed__1;
x_29 = lean_array_push(x_28, x_3);
lean_inc(x_11);
x_30 = l_Lean_Meta_mkForallFVars(x_29, x_26, x_23, x_24, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_4);
x_33 = l_Lean_Meta_mkForallFVars(x_4, x_31, x_23, x_24, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 2;
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_6, x_34, x_36, x_21, x_37, x_11, x_12, x_13, x_14, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_39);
x_41 = l_Lean_mkAppN(x_39, x_7);
x_42 = l_Lean_mkApp(x_41, x_8);
x_43 = l_Lean_mkAppN(x_42, x_9);
x_44 = l_Lean_Meta_assignExprMVar(x_2, x_43, x_11, x_12, x_13, x_14, x_40);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Expr_mvarId_x21(x_39);
lean_dec(x_39);
x_47 = lean_array_get_size(x_4);
lean_dec(x_4);
x_48 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_49 = l_Lean_Meta_introNCore(x_46, x_47, x_48, x_23, x_24, x_11, x_12, x_13, x_14, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lean_Meta_intro1Core(x_53, x_24, x_11, x_12, x_13, x_14, x_51);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_get_size(x_16);
lean_dec(x_16);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_54, 0, x_60);
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_54, 0);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_54);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_array_get_size(x_16);
lean_dec(x_16);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_52);
lean_ctor_set(x_66, 2, x_63);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_52);
lean_dec(x_16);
x_68 = !lean_is_exclusive(x_54);
if (x_68 == 0)
{
return x_54;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_54, 0);
x_70 = lean_ctor_get(x_54, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_54);
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
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_72 = !lean_is_exclusive(x_49);
if (x_72 == 0)
{
return x_49;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_49, 0);
x_74 = lean_ctor_get(x_49, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_49);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_33);
if (x_76 == 0)
{
return x_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_33, 0);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_33);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_30);
if (x_80 == 0)
{
return x_30;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_30, 0);
x_82 = lean_ctor_get(x_30, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_30);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_25);
if (x_84 == 0)
{
return x_25;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_25, 0);
x_86 = lean_ctor_get(x_25, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_25);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_20);
if (x_88 == 0)
{
return x_20;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_20, 0);
x_90 = lean_ctor_get(x_20, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_20);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_17);
if (x_92 == 0)
{
return x_17;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_17, 0);
x_94 = lean_ctor_get(x_17, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_17);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
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
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1), 15, 9);
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
x_25 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__2___rarg(x_23, x_24, x_19, x_22, x_10, x_11, x_12, x_13, x_18);
return x_25;
}
else
{
uint8_t x_26; 
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_7);
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
x_18 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__2___rarg(x_15, x_17, x_14, x_16, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_Array_extract___rarg(x_1, x_16, x_14);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_extract___rarg(x_1, x_19, x_18);
x_21 = l_Lean_mkAppN(x_3, x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_22 = lean_infer_type(x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_26 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_23, x_25, x_9, x_10, x_11, x_12, x_24);
return x_26;
}
else
{
uint8_t x_27; 
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
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed inductive datatype");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_9);
x_15 = lean_array_get_size(x_1);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_nat_dec_eq(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3;
x_21 = lean_box(0);
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_5, x_20, x_21, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
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
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive type expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("indexed inductive type expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
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
x_19 = lean_environment_find(x_18, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_21 = lean_box(0);
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_20, x_21, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
x_29 = lean_box(0);
x_30 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_28, x_29, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
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
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(x_7, x_24, x_6, x_5, x_1, x_2, x_3, x_4, x_35, x_9, x_10, x_11, x_12, x_17);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_37 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_38 = lean_box(0);
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_37, x_38, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
return x_39;
}
}
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_array_set(x_7, x_8, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_8, x_43);
lean_dec(x_8);
x_6 = x_40;
x_7 = x_42;
x_8 = x_44;
goto _start;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_47 = lean_box(0);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_46, x_47, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("generalizeIndices");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_3);
x_15 = l_Lean_Meta_getLocalDecl(x_2, x_3, x_4, x_5, x_6, x_14);
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
x_23 = l_Lean_Expr_getAppNumArgsAux(x_20, x_22);
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
x_9 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
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
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_nminors___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_nminors___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Cases_Context_nminors___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_sub(x_3, x_4);
x_6 = l_Array_extract___rarg(x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Cases_Context_majorTypeIndices___default(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("casesOn");
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
x_16 = lean_environment_find(x_15, x_11);
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
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = lean_environment_find(x_1, x_29);
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
lean_inc(x_4);
x_39 = l_Array_extract___rarg(x_4, x_38, x_20);
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
lean_inc(x_4);
x_48 = l_Array_extract___rarg(x_4, x_47, x_20);
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
x_56 = lean_environment_find(x_55, x_11);
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
x_71 = lean_name_mk_string(x_69, x_70);
x_72 = lean_environment_find(x_1, x_71);
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
lean_inc(x_4);
x_82 = l_Array_extract___rarg(x_4, x_81, x_61);
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
x_18 = l_Lean_Meta_getLocalDecl(x_1, x_2, x_3, x_4, x_5, x_10);
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
x_26 = l_Lean_Expr_getAppNumArgsAux(x_23, x_25);
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
x_51 = l_Lean_Meta_getLocalDecl(x_1, x_2, x_3, x_4, x_5, x_41);
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
x_59 = l_Lean_Expr_getAppNumArgsAux(x_56, x_58);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
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
x_10 = x_3 + x_9;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_4 + x_9;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_2, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_6, x_1, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Lean_MetavarContext_getExprAssignment_x3f(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_MetavarContext_getDecl(x_3, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_33, x_5);
return x_34;
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_3);
x_37 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_36, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Expr_isApp(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_35, x_40);
return x_42;
}
else
{
x_4 = x_35;
x_5 = x_40;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec(x_4);
lean_inc(x_3);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_48, x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_49, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 2);
lean_inc(x_60);
lean_dec(x_4);
lean_inc(x_3);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_59, x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_60, x_64);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_60);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_70, x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_72, x_80);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_72);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 0);
lean_dec(x_83);
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_73, 0);
lean_dec(x_87);
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 10:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_dec(x_4);
x_91 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_90, x_5);
return x_91;
}
case 11:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
lean_dec(x_4);
x_93 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_92, x_5);
return x_93;
}
default: 
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_1, x_2, x_3, x_4, x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_4 + x_9;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_2, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_6, x_1, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Lean_MetavarContext_getExprAssignment_x3f(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_MetavarContext_getDecl(x_3, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_33, x_5);
return x_34;
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_3);
x_37 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_36, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Expr_isApp(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_35, x_40);
return x_42;
}
else
{
x_4 = x_35;
x_5 = x_40;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec(x_4);
lean_inc(x_3);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_48, x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_49, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 2);
lean_inc(x_60);
lean_dec(x_4);
lean_inc(x_3);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_59, x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_60, x_64);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_60);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_70, x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_72, x_80);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_72);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 0);
lean_dec(x_83);
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_73, 0);
lean_dec(x_87);
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 10:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_dec(x_4);
x_91 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_90, x_5);
return x_91;
}
case 11:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
lean_dec(x_4);
x_93 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_92, x_5);
return x_93;
}
default: 
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_3, x_4, x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_4 + x_9;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_2, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_6, x_1, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Lean_MetavarContext_getExprAssignment_x3f(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_MetavarContext_getDecl(x_3, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_33, x_5);
return x_34;
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_3);
x_37 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_36, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Expr_isApp(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_35, x_40);
return x_42;
}
else
{
x_4 = x_35;
x_5 = x_40;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec(x_4);
lean_inc(x_3);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_48, x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_49, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 2);
lean_inc(x_60);
lean_dec(x_4);
lean_inc(x_3);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_59, x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_60, x_64);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_60);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_70, x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_72, x_80);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_72);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 0);
lean_dec(x_83);
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_73, 0);
lean_dec(x_87);
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 10:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_dec(x_4);
x_91 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_90, x_5);
return x_91;
}
case 11:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
lean_dec(x_4);
x_93 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_92, x_5);
return x_93;
}
default: 
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_4 + x_9;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_2, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_6, x_1, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Lean_MetavarContext_getExprAssignment_x3f(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_MetavarContext_getDecl(x_3, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_33, x_5);
return x_34;
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_3);
x_37 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_36, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Expr_isApp(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_35, x_40);
return x_42;
}
else
{
x_4 = x_35;
x_5 = x_40;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec(x_4);
lean_inc(x_3);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_48, x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_49, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 2);
lean_inc(x_60);
lean_dec(x_4);
lean_inc(x_3);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_59, x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_60, x_64);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_60);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_70, x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_72, x_80);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_72);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 0);
lean_dec(x_83);
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_73, 0);
lean_dec(x_87);
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 10:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_dec(x_4);
x_91 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_90, x_5);
return x_91;
}
case 11:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
lean_dec(x_4);
x_93 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_92, x_5);
return x_93;
}
default: 
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_4 + x_9;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_2, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_6, x_1, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Lean_MetavarContext_getExprAssignment_x3f(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_MetavarContext_getDecl(x_3, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_33, x_5);
return x_34;
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_3);
x_37 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_36, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Expr_isApp(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_35, x_40);
return x_42;
}
else
{
x_4 = x_35;
x_5 = x_40;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec(x_4);
lean_inc(x_3);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_48, x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_49, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 2);
lean_inc(x_60);
lean_dec(x_4);
lean_inc(x_3);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_59, x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_60, x_64);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_60);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_70, x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_72, x_80);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_72);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 0);
lean_dec(x_83);
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_73, 0);
lean_dec(x_87);
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 10:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_dec(x_4);
x_91 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_90, x_5);
return x_91;
}
case 11:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
lean_dec(x_4);
x_93 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_92, x_5);
return x_93;
}
default: 
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_3, x_4, x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_4 + x_9;
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
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(x_1, x_2, x_14, x_21, x_22);
lean_dec(x_14);
return x_23;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_4 + x_8;
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
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = 1;
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_12, x_1, x_18, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
goto _start;
}
}
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(x_1, x_2, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_2, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_6, x_1, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Lean_MetavarContext_getExprAssignment_x3f(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_MetavarContext_getDecl(x_3, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_29);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_33, x_5);
return x_34;
}
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_3);
x_37 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_36, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Expr_isApp(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_35, x_40);
return x_42;
}
else
{
x_4 = x_35;
x_5 = x_40;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
lean_dec(x_4);
lean_inc(x_3);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_48, x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_49, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_49);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 2);
lean_inc(x_60);
lean_dec(x_4);
lean_inc(x_3);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_59, x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_60, x_64);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_60);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_dec(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_dec(x_4);
lean_inc(x_3);
x_73 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_70, x_5);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_3);
x_77 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_72, x_80);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_72);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 0);
lean_dec(x_83);
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_73, 0);
lean_dec(x_87);
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 10:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_dec(x_4);
x_91 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_90, x_5);
return x_91;
}
case 11:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
lean_dec(x_4);
x_93 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_92, x_5);
return x_93;
}
default: 
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_4, x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
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
x_10 = x_3 + x_9;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_5, x_6);
lean_inc(x_4);
x_10 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = x_6 + x_11;
x_6 = x_12;
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
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = 0;
return x_15;
}
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = x_6 == x_7;
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_uget(x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = x_6 + x_15;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_65 = l_Lean_LocalDecl_fvarId(x_18);
x_66 = lean_ctor_get(x_1, 3);
x_67 = l_Lean_LocalDecl_fvarId(x_66);
x_68 = lean_name_eq(x_65, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_3);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_65);
x_71 = lean_box(0);
x_19 = x_71;
goto block_64;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_3, x_3);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_box(0);
x_19 = x_73;
goto block_64;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_3);
x_76 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_65, x_2, x_74, x_75);
lean_dec(x_65);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_box(0);
x_19 = x_77;
goto block_64;
}
else
{
lean_object* x_78; 
lean_dec(x_18);
x_78 = lean_box(0);
x_8 = x_78;
goto block_12;
}
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_65);
lean_dec(x_18);
x_79 = lean_box(0);
x_8 = x_79;
goto block_12;
}
block_64:
{
lean_dec(x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_hasFVar(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_4);
x_23 = 1;
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_2, x_3, x_4, x_20, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_4);
x_28 = 1;
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_8 = x_29;
goto block_12;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_31 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_2, x_3, x_4, x_20, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_4);
x_34 = 1;
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_box(0);
x_8 = x_35;
goto block_12;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_57; 
x_36 = lean_ctor_get(x_18, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_18, 4);
lean_inc(x_37);
lean_dec(x_18);
x_57 = l_Lean_Expr_hasFVar(x_36);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Expr_hasMVar(x_36);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_36);
x_59 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__2;
x_38 = x_59;
goto block_56;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_2, x_3, x_4, x_36, x_60);
x_38 = x_61;
goto block_56;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_2, x_3, x_4, x_36, x_62);
x_38 = x_63;
goto block_56;
}
block_56:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Expr_hasFVar(x_37);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_37);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_4);
x_44 = 1;
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_inc(x_4);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_2, x_3, x_4, x_37, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_4);
x_48 = 1;
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_box(0);
x_8 = x_49;
goto block_12;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_inc(x_4);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_2, x_3, x_4, x_37, x_41);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
lean_dec(x_4);
x_53 = 1;
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_8 = x_54;
goto block_12;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_38);
lean_dec(x_37);
x_55 = lean_box(0);
x_8 = x_55;
goto block_12;
}
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_4);
x_80 = 0;
return x_80;
}
block_12:
{
size_t x_9; size_t x_10; 
lean_dec(x_8);
x_9 = 1;
x_10 = x_6 + x_9;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(x_1, x_2, x_3, x_4, x_6, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
x_20 = 0;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
x_22 = 0;
return x_22;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_2, x_3, x_4, x_16, x_23, x_24);
lean_dec(x_16);
return x_25;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = x_6 == x_7;
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_uget(x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = x_6 + x_15;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_65 = l_Lean_LocalDecl_fvarId(x_18);
x_66 = lean_ctor_get(x_1, 3);
x_67 = l_Lean_LocalDecl_fvarId(x_66);
x_68 = lean_name_eq(x_65, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_lt(x_69, x_3);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_65);
x_71 = lean_box(0);
x_19 = x_71;
goto block_64;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_3, x_3);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_65);
x_73 = lean_box(0);
x_19 = x_73;
goto block_64;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_3);
x_76 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_65, x_2, x_74, x_75);
lean_dec(x_65);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_box(0);
x_19 = x_77;
goto block_64;
}
else
{
lean_object* x_78; 
lean_dec(x_18);
x_78 = lean_box(0);
x_8 = x_78;
goto block_12;
}
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_65);
lean_dec(x_18);
x_79 = lean_box(0);
x_8 = x_79;
goto block_12;
}
block_64:
{
lean_dec(x_19);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_hasFVar(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_4);
x_23 = 1;
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_2, x_3, x_4, x_20, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_4);
x_28 = 1;
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_8 = x_29;
goto block_12;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_31 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_2, x_3, x_4, x_20, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_4);
x_34 = 1;
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_box(0);
x_8 = x_35;
goto block_12;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_57; 
x_36 = lean_ctor_get(x_18, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_18, 4);
lean_inc(x_37);
lean_dec(x_18);
x_57 = l_Lean_Expr_hasFVar(x_36);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Expr_hasMVar(x_36);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_36);
x_59 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__2;
x_38 = x_59;
goto block_56;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_61 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_2, x_3, x_4, x_36, x_60);
x_38 = x_61;
goto block_56;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1;
lean_inc(x_4);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_2, x_3, x_4, x_36, x_62);
x_38 = x_63;
goto block_56;
}
block_56:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Expr_hasFVar(x_37);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_37);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_4);
x_44 = 1;
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_inc(x_4);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_2, x_3, x_4, x_37, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_4);
x_48 = 1;
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_box(0);
x_8 = x_49;
goto block_12;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_inc(x_4);
x_50 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_2, x_3, x_4, x_37, x_41);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
lean_dec(x_4);
x_53 = 1;
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_8 = x_54;
goto block_12;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_38);
lean_dec(x_37);
x_55 = lean_box(0);
x_8 = x_55;
goto block_12;
}
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_4);
x_80 = 0;
return x_80;
}
block_12:
{
size_t x_9; size_t x_10; 
lean_dec(x_8);
x_9 = 1;
x_10 = x_6 + x_9;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_inc(x_4);
x_7 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_14 = 0;
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(x_1, x_2, x_3, x_4, x_8, x_15, x_16);
lean_dec(x_8);
return x_17;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_add(x_8, x_7);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedExpr;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_array_get(x_11, x_1, x_10);
lean_dec(x_10);
x_14 = lean_expr_eqv(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_nat_add(x_7, x_6);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(x_1, x_9, x_9, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_add(x_8, x_7);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedExpr;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_array_get(x_11, x_1, x_10);
lean_dec(x_10);
x_14 = lean_expr_eqv(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_nat_add(x_7, x_6);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(x_1, x_9, x_9, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
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
x_9 = x_2 + x_8;
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
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_add(x_8, x_7);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedExpr;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_array_get(x_11, x_1, x_10);
lean_dec(x_10);
x_14 = lean_expr_eqv(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_nat_add(x_7, x_6);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_8);
lean_inc(x_9);
x_10 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(x_1, x_9, x_9, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 0;
return x_13;
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
lean_object* x_9; lean_object* x_10; lean_object* x_36; uint8_t x_37; 
x_9 = lean_array_get_size(x_7);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_9);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc(x_9);
x_38 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(x_7, x_9, x_9);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_10 = x_39;
goto block_35;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_2);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_6);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_9, x_9);
if (x_43 == 0)
{
uint8_t x_44; 
lean_inc(x_9);
x_44 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(x_7, x_9, x_9);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_10 = x_45;
goto block_35;
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_2);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_6);
return x_48;
}
}
else
{
size_t x_49; size_t x_50; uint8_t x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_9);
x_51 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(x_7, x_49, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_inc(x_9);
x_52 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(x_7, x_9, x_9);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_10 = x_53;
goto block_35;
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_9);
lean_dec(x_2);
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_6);
return x_56;
}
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_9);
lean_dec(x_2);
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_6);
return x_59;
}
}
}
block_35:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_st_ref_get(x_5, x_6);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_7, x_9, x_17, x_18);
lean_dec(x_9);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
x_28 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_7, x_9, x_26, x_27);
lean_dec(x_9);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
}
}
else
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_2);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_6);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_array_uget(x_1, x_2);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 2);
lean_inc(x_11);
x_24 = l_Lean_Meta_FVarSubst_get(x_23, x_11);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_saveState___rarg(x_6, x_7, x_8, x_9);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Meta_clear(x_21, x_25, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_4, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_11, x_23);
lean_dec(x_11);
lean_ctor_set(x_18, 2, x_35);
lean_ctor_set(x_18, 0, x_33);
x_12 = x_4;
x_13 = x_34;
goto block_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_11, x_23);
lean_dec(x_11);
lean_ctor_set(x_18, 2, x_38);
lean_ctor_set(x_18, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_19);
x_12 = x_39;
x_13 = x_37;
goto block_17;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_18);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_11);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = l_Lean_Meta_SavedState_restore(x_27, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_27);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_12 = x_4;
x_13 = x_42;
goto block_17;
}
}
else
{
lean_dec(x_24);
lean_free_object(x_18);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_11);
x_12 = x_4;
x_13 = x_9;
goto block_17;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
x_45 = lean_ctor_get(x_18, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
lean_inc(x_11);
x_46 = l_Lean_Meta_FVarSubst_get(x_45, x_11);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Meta_saveState___rarg(x_6, x_7, x_8, x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_51 = l_Lean_Meta_clear(x_43, x_47, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_52 = x_4;
} else {
 lean_dec_ref(x_4);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_11, x_45);
lean_dec(x_11);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_55);
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_19);
x_12 = x_57;
x_13 = x_54;
goto block_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_19);
lean_dec(x_11);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_Meta_SavedState_restore(x_49, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_49);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_12 = x_4;
x_13 = x_60;
goto block_17;
}
}
else
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_19);
lean_dec(x_11);
x_12 = x_4;
x_13 = x_9;
goto block_17;
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = x_2 + x_14;
x_2 = x_15;
x_4 = x_12;
x_9 = x_13;
goto _start;
}
}
else
{
lean_object* x_61; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_9);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 < x_2;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = x_4;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_16 = x_13;
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_14, x_17);
if (x_18 == 0)
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_19 = 1;
x_20 = x_3 + x_19;
x_21 = x_16;
x_22 = lean_array_uset(x_15, x_3, x_21);
x_3 = x_20;
x_4 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_17, x_17);
if (x_24 == 0)
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
x_25 = 1;
x_26 = x_3 + x_25;
x_27 = x_16;
x_28 = lean_array_uset(x_15, x_3, x_27);
x_3 = x_26;
x_4 = x_28;
goto _start;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_17);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(x_1, x_30, x_31, x_16, x_5, x_6, x_7, x_8, x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = 1;
x_36 = x_3 + x_35;
x_37 = x_33;
x_38 = lean_array_uset(x_15, x_3, x_37);
x_3 = x_36;
x_4 = x_38;
x_9 = x_34;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = x_2;
x_12 = lean_box_usize(x_10);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1;
x_14 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed), 9, 4);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_11);
x_15 = x_14;
x_16 = lean_apply_5(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
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
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_7, x_13);
lean_dec(x_7);
x_15 = lean_array_fget(x_6, x_8);
x_16 = l_Lean_instInhabitedName;
x_17 = lean_array_get(x_16, x_2, x_8);
lean_inc(x_4);
lean_inc(x_17);
x_18 = l_Lean_mkConst(x_17, x_4);
lean_inc(x_5);
x_19 = l_Lean_mkAppN(x_18, x_5);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 2);
lean_inc(x_21);
x_23 = l_Lean_mkAppN(x_19, x_21);
lean_inc(x_3);
x_24 = l_Lean_Meta_FVarSubst_insert(x_22, x_3, x_23);
lean_ctor_set(x_15, 2, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_17);
x_26 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_27 = lean_array_push(x_10, x_25);
x_7 = x_14;
x_8 = x_26;
x_9 = lean_box(0);
x_10 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
x_31 = lean_ctor_get(x_15, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
lean_inc(x_30);
x_32 = l_Lean_mkAppN(x_19, x_30);
lean_inc(x_3);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_3, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_17);
x_36 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_37 = lean_array_push(x_10, x_35);
x_7 = x_14;
x_8 = x_36;
x_9 = lean_box(0);
x_10 = x_37;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
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
x_9 = l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_1, x_6, x_8, lean_box(0), x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
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
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_heqToEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_LocalDecl_fvarId(x_2);
lean_inc(x_8);
x_9 = l_Lean_mkFVar(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Meta_mkEqOfHEq(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_13 = lean_infer_type(x_11, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_whnf(x_14, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_userName(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Meta_assert(x_1, x_19, x_17, x_11, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_clear(x_21, x_8, x_3, x_4, x_5, x_6, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_heqToEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_heqToEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1___at_Lean_Meta_Cases_unifyEqs_substEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_saveState___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_substCore(x_3, x_2, x_4, x_1, x_13, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Meta_SavedState_restore(x_11, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_11);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs_substEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dependent elimination failed, failed to solve equation");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs_substEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_unifyEqs_substEq___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_substEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1___at_Lean_Meta_Cases_unifyEqs_substEq___spec__2(x_2, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_isExprDefEq(x_7, x_8, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_LocalDecl_type(x_6);
lean_dec(x_6);
x_23 = l_Lean_indentExpr(x_22);
x_24 = l_Lean_Meta_Cases_unifyEqs_substEq___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3(x_27, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Meta_clear(x_5, x_4, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_1, x_33);
lean_dec(x_1);
x_35 = l_Lean_Meta_Cases_unifyEqs(x_34, x_31, x_2, x_3, x_10, x_11, x_12, x_13, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_dec(x_15);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_1, x_48);
lean_dec(x_1);
x_50 = l_Lean_Meta_Cases_unifyEqs(x_49, x_47, x_46, x_3, x_10, x_11, x_12, x_13, x_45);
return x_50;
}
}
}
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_getLocalDecl(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
x_15 = l_Lean_Expr_isHEq(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof___closed__6;
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Expr_isAppOfArity(x_14, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_indentExpr(x_14);
x_20 = l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3(x_23, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Expr_appFn_x21(x_14);
x_26 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_26);
x_28 = l_Lean_Meta_instantiateMVars(x_26, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_27);
x_31 = l_Lean_Meta_instantiateMVars(x_27, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
lean_inc(x_6);
x_36 = l_Lean_Meta_getLocalDecl(x_34, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_6);
x_39 = l_Lean_Meta_getLocalDecl(x_35, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_LocalDecl_index(x_37);
lean_dec(x_37);
x_43 = l_Lean_LocalDecl_index(x_40);
lean_dec(x_40);
x_44 = lean_nat_dec_lt(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
x_45 = l_Lean_Meta_Cases_unifyEqs_substEq(x_2, x_3, x_4, x_1, x_5, x_12, x_26, x_27, x_44, x_6, x_7, x_8, x_9, x_41);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
return x_36;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_36, 0);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_36);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
lean_dec(x_32);
lean_dec(x_29);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_dec(x_31);
x_55 = 0;
x_56 = l_Lean_Meta_Cases_unifyEqs_substEq(x_2, x_3, x_4, x_1, x_5, x_12, x_26, x_27, x_55, x_6, x_7, x_8, x_9, x_54);
return x_56;
}
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_29);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_dec(x_31);
x_59 = 1;
x_60 = l_Lean_Meta_Cases_unifyEqs_substEq(x_2, x_3, x_4, x_1, x_5, x_12, x_26, x_27, x_59, x_6, x_7, x_8, x_9, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_27);
lean_dec(x_26);
x_61 = lean_ctor_get(x_31, 1);
lean_inc(x_61);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_57);
lean_inc(x_29);
x_62 = l_Lean_Meta_isExprDefEq(x_29, x_57, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Meta_Cases_unifyEqs_injection(x_2, x_3, x_4, x_1, x_5, x_12, x_29, x_57, x_6, x_7, x_8, x_9, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_57);
lean_dec(x_29);
lean_dec(x_12);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_68 = l_Lean_Meta_clear(x_5, x_1, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_2, x_71);
lean_dec(x_2);
x_73 = l_Lean_Meta_Cases_unifyEqs(x_72, x_69, x_3, x_4, x_6, x_7, x_8, x_9, x_70);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_68);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_57);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_62);
if (x_78 == 0)
{
return x_62;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_62, 0);
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_62);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_28);
if (x_86 == 0)
{
return x_28;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_28, 0);
x_88 = lean_ctor_get(x_28, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_28);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_14);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_90 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_heqToEq(x_5, x_12, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Meta_Cases_unifyEqs(x_2, x_91, x_3, x_4, x_6, x_7, x_8, x_9, x_92);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
return x_90;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_90, 0);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_90);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_11);
if (x_98 == 0)
{
return x_11;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_11, 0);
x_100 = lean_ctor_get(x_11, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_11);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_intro1Core(x_2, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_unifyEqs___lambda__1), 10, 5);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_17);
x_19 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_17, x_18, x_5, x_6, x_7, x_8, x_15);
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
lean_dec(x_1);
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
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs_injection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nat case ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_unifyEqs_injection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_unifyEqs_injection___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_injection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_85; 
x_14 = lean_st_ref_get(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_17);
x_85 = l_Lean_Expr_isConstructorApp(x_17, x_7);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_17);
x_86 = lean_box(0);
x_18 = x_86;
goto block_84;
}
else
{
uint8_t x_87; 
x_87 = l_Lean_Expr_isConstructorApp(x_17, x_8);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_box(0);
x_18 = x_88;
goto block_84;
}
else
{
lean_object* x_89; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_89 = l_Lean_Meta_injectionCore(x_5, x_4, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_89, 0, x_93);
return x_89;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
lean_dec(x_89);
x_98 = lean_ctor_get(x_90, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_90, 1);
lean_inc(x_99);
lean_dec(x_90);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_1, x_100);
lean_dec(x_1);
x_102 = lean_nat_add(x_101, x_99);
lean_dec(x_99);
lean_dec(x_101);
x_103 = l_Lean_Meta_Cases_unifyEqs(x_102, x_98, x_2, x_3, x_9, x_10, x_11, x_12, x_97);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_89);
if (x_104 == 0)
{
return x_89;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_89, 0);
x_106 = lean_ctor_get(x_89, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_89);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
block_84:
{
lean_object* x_19; 
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_19 = lean_whnf(x_7, x_9, x_10, x_11, x_12, x_16);
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
lean_inc(x_8);
x_22 = lean_whnf(x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_51; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_51 = lean_expr_eqv(x_20, x_7);
lean_dec(x_7);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_8);
x_52 = lean_box(0);
x_25 = x_52;
goto block_50;
}
else
{
uint8_t x_53; 
x_53 = lean_expr_eqv(x_23, x_8);
lean_dec(x_8);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_25 = x_54;
goto block_50;
}
else
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = l_Lean_LocalDecl_type(x_6);
lean_dec(x_6);
x_56 = l_Lean_indentExpr(x_55);
x_57 = l_Lean_Meta_Cases_unifyEqs_substEq___closed__2;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3(x_60, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
lean_dec(x_3);
x_63 = l_Lean_LocalDecl_type(x_6);
lean_dec(x_6);
x_64 = l_Lean_indentExpr(x_63);
x_65 = l_Lean_Meta_Cases_unifyEqs_substEq___closed__2;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Meta_Cases_unifyEqs_injection___closed__2;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_mkConst(x_62, x_69);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3(x_74, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_75;
}
}
}
block_50:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_25);
lean_inc(x_4);
x_26 = l_Lean_mkFVar(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l_Lean_Meta_mkEq(x_20, x_23, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_LocalDecl_userName(x_6);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_31 = l_Lean_Meta_assert(x_5, x_30, x_28, x_26, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_34 = l_Lean_Meta_clear(x_32, x_4, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_Cases_unifyEqs(x_1, x_35, x_2, x_3, x_9, x_10, x_11, x_12, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
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
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
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
uint8_t x_76; 
lean_dec(x_20);
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
x_76 = !lean_is_exclusive(x_22);
if (x_76 == 0)
{
return x_22;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_22, 0);
x_78 = lean_ctor_get(x_22, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_22);
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
x_80 = !lean_is_exclusive(x_19);
if (x_80 == 0)
{
return x_19;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_19, 0);
x_82 = lean_ctor_get(x_19, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_19);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1___at_Lean_Meta_Cases_unifyEqs_substEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_observing_x3f___at_Lean_Meta_Cases_unifyEqs_substEq___spec__1___at_Lean_Meta_Cases_unifyEqs_substEq___spec__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Cases_unifyEqs_substEq___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_unifyEqs_substEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l_Lean_Meta_Cases_unifyEqs_substEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
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
x_19 = l_Lean_Meta_Cases_unifyEqs(x_1, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10);
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
x_23 = x_3 + x_22;
x_3 = x_23;
x_10 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
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
x_30 = lean_array_get_size(x_29);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = x_29;
x_34 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(x_28, x_31, x_32, x_33);
x_35 = x_34;
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_12, 0, x_36);
x_37 = lean_array_push(x_5, x_12);
x_38 = 1;
x_39 = x_3 + x_38;
x_3 = x_39;
x_5 = x_37;
x_10 = x_26;
goto _start;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 2);
lean_inc(x_48);
lean_inc(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_50 = l_Lean_Meta_Cases_unifyEqs(x_1, x_47, x_48, x_49, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_46);
lean_dec(x_45);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = 1;
x_54 = x_3 + x_53;
x_3 = x_54;
x_10 = x_52;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; 
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_array_get_size(x_60);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = 0;
x_64 = x_60;
x_65 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs___spec__1(x_59, x_62, x_63, x_64);
x_66 = x_65;
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_59);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_46);
x_69 = lean_array_push(x_5, x_68);
x_70 = 1;
x_71 = x_3 + x_70;
x_3 = x_71;
x_5 = x_69;
x_10 = x_57;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_73 = lean_ctor_get(x_50, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_50, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_75 = x_50;
} else {
 lean_dec_ref(x_50);
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
lean_object* x_77; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_5);
lean_ctor_set(x_77, 1, x_10);
return x_77;
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
x_14 = l_Lean_Meta_getInductiveUniverseAndParams(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_casesOnSuffix;
x_23 = lean_name_mk_string(x_21, x_22);
x_24 = lean_ctor_get(x_19, 4);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_List_redLength___rarg(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
x_27 = l_List_toArrayAux___rarg(x_24, x_26);
lean_inc(x_4);
x_28 = l_Lean_Meta_induction(x_3, x_4, x_23, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_30, x_27, x_4, x_17, x_18);
lean_dec(x_27);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_32, x_27, x_4, x_17, x_18);
lean_dec(x_27);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_10 = l_Lean_mkFVar(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1), 10, 5);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_3);
x_12 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_10, x_11, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_1, x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyCasesEqs(x_18, x_16, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_16);
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
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not applicable to the given hypothesis");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__5;
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cases");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__7;
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after generalizeIndices\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(x_3, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Cases_cases___lambda__2___closed__3;
x_16 = lean_box(0);
x_17 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_15, x_16, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Cases_cases___lambda__2___closed__9;
x_43 = lean_st_ref_get(x_8, x_26);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = 0;
x_28 = x_48;
x_29 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_27, x_5, x_6, x_7, x_8, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_28 = x_53;
x_29 = x_52;
goto block_42;
}
block_42:
{
if (x_28 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Cases_cases___lambda__1(x_25, x_4, x_19, x_30, x_5, x_6, x_7, x_8, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Meta_Cases_cases___lambda__2___closed__11;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_27, x_37, x_5, x_6, x_7, x_8, x_29);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Cases_cases___lambda__1(x_25, x_4, x_19, x_39, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_39);
return x_41;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_24);
if (x_54 == 0)
{
return x_24;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_24, 0);
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_24);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
x_58 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_3, x_4, x_19, x_5, x_6, x_7, x_8, x_18);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_12);
if (x_59 == 0)
{
return x_12;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_12, 0);
x_61 = lean_ctor_get(x_12, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_12);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Meta_Cases_cases___closed__1;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__2), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
x_11 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_casesRec___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2___at_Lean_Meta_casesRec___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_array_to_list(lean_box(0), x_14);
x_16 = lean_box(0);
x_17 = l_List_mapTRAux___at_Lean_Meta_casesRec___spec__1(x_15, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
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
x_21 = lean_array_to_list(lean_box(0), x_19);
x_22 = lean_box(0);
x_23 = l_List_mapTRAux___at_Lean_Meta_casesRec___spec__1(x_21, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
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
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_8 < x_7;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_6, x_8);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_19);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5(x_1, x_2, x_3, x_4, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_9, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_19);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_5);
x_31 = 1;
x_32 = x_8 + x_31;
x_8 = x_32;
x_14 = x_29;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_9);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_38);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5(x_1, x_2, x_3, x_4, x_17, x_38, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_inc(x_5);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_47);
x_49 = 1;
x_50 = x_8 + x_49;
x_8 = x_50;
x_9 = x_48;
x_14 = x_46;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_54 = x_39;
} else {
 lean_dec_ref(x_39);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_7 < x_6;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_18 = x_8;
} else {
 lean_dec_ref(x_8);
 x_18 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; 
lean_inc(x_17);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_17);
x_19 = x_30;
x_20 = x_13;
goto block_29;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
x_33 = lean_apply_6(x_1, x_32, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_16);
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_3);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_3);
x_19 = x_37;
x_20 = x_36;
goto block_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
x_40 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_41 = l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2___at_Lean_Meta_casesRec___spec__3(x_2, x_39, x_40, x_9, x_10, x_11, x_12, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_16);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_3);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_3);
x_19 = x_44;
x_20 = x_43;
goto block_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
lean_ctor_set(x_16, 0, x_42);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_16);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_19 = x_48;
x_20 = x_45;
goto block_29;
}
}
}
else
{
uint8_t x_49; 
lean_free_object(x_16);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
return x_33;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_16, 0);
lean_inc(x_53);
lean_dec(x_16);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_53);
x_54 = lean_apply_6(x_1, x_53, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_inc(x_3);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_3);
x_19 = x_58;
x_20 = x_57;
goto block_29;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = l_Lean_LocalDecl_fvarId(x_53);
lean_dec(x_53);
x_61 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_62 = l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2___at_Lean_Meta_casesRec___spec__3(x_2, x_60, x_61, x_9, x_10, x_11, x_12, x_59);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_3);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_3);
x_19 = x_65;
x_20 = x_64;
goto block_29;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_19 = x_70;
x_20 = x_66;
goto block_29;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_53);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
block_29:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
if (lean_is_scalar(x_18)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_18;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_17);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
lean_inc(x_4);
if (lean_is_scalar(x_18)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_18;
}
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = x_7 + x_26;
x_7 = x_27;
x_8 = x_25;
x_13 = x_20;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_array_get_size(x_12);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__6(x_1, x_2, x_3, x_4, x_13, x_12, x_16, x_17, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
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
x_24 = l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5___lambda__1(x_22, x_23, x_7, x_8, x_9, x_10, x_21);
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
lean_dec(x_4);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
x_38 = lean_array_get_size(x_35);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__7(x_1, x_2, x_3, x_36, x_35, x_39, x_40, x_37, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_35);
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
x_47 = l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5___lambda__1(x_45, x_46, x_7, x_8, x_9, x_10, x_44);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_7 < x_6;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_18 = x_8;
} else {
 lean_dec_ref(x_8);
 x_18 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_31; 
lean_inc(x_17);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_17);
x_19 = x_31;
x_20 = x_13;
goto block_30;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_33);
x_34 = lean_apply_6(x_1, x_33, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_free_object(x_16);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_3);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_3);
x_19 = x_38;
x_20 = x_37;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_41 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_42 = l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2___at_Lean_Meta_casesRec___spec__3(x_2, x_40, x_41, x_9, x_10, x_11, x_12, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_free_object(x_16);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_3);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_3);
x_19 = x_45;
x_20 = x_44;
goto block_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
lean_ctor_set(x_16, 0, x_43);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_16);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_19 = x_49;
x_20 = x_46;
goto block_30;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_16);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_34);
if (x_50 == 0)
{
return x_34;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_34, 0);
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_34);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
lean_dec(x_16);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_54);
x_55 = lean_apply_6(x_1, x_54, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_3);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_3);
x_19 = x_59;
x_20 = x_58;
goto block_30;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = l_Lean_LocalDecl_fvarId(x_54);
lean_dec(x_54);
x_62 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewEqs___rarg___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_63 = l_Lean_observing_x3f___at_Lean_Meta_casesRec___spec__2___at_Lean_Meta_casesRec___spec__3(x_2, x_61, x_62, x_9, x_10, x_11, x_12, x_60);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_3);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_3);
x_19 = x_66;
x_20 = x_65;
goto block_30;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_19 = x_71;
x_20 = x_67;
goto block_30;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_54);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_55, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_55, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_74 = x_55;
} else {
 lean_dec_ref(x_55);
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
block_30:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (lean_is_scalar(x_18)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_18;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_17);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
lean_inc(x_4);
if (lean_is_scalar(x_18)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_18;
}
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = x_7 + x_27;
x_7 = x_28;
x_8 = x_26;
x_13 = x_20;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
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
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_array_get_size(x_22);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__8(x_1, x_2, x_3, x_23, x_22, x_26, x_27, x_24, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_22);
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
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Meta_casesRec___lambda__1___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_casesRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_casesRec___lambda__1___closed__1;
x_12 = l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4(x_1, x_2, x_11, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_casesRec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_casesRec___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_casesRec___lambda__2), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_saturate(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__7(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forInAux___at_Lean_Meta_casesRec___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_casesRec___spec__8(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forIn___at_Lean_Meta_casesRec___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_casesAnd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_casesAnd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_casesAnd___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesAnd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_LocalDecl_type(x_1);
x_8 = l_Lean_Meta_instantiateMVars(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_casesAnd___lambda__1___closed__2;
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
x_17 = l_Lean_Meta_casesAnd___lambda__1___closed__2;
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
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_casesAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_casesAnd___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_casesAnd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected number of goals");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_casesAnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_casesAnd___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_casesAnd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_casesAnd___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_casesAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_casesAnd___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_casesRec(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_casesAnd___closed__4;
x_12 = l_Lean_Meta_exactlyOne(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_casesAnd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_casesAnd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEqs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_LocalDecl_type(x_1);
x_8 = l_Lean_Meta_instantiateMVars(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
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
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substEqs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_substEqs___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_substEqs___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_casesRec(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_casesAnd___closed__4;
x_12 = l_Lean_Meta_exactlyOne(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substEqs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_substEqs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases_toByCasesSubgoal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
static lean_object* _init_l_Lean_Meta_byCases_toByCasesSubgoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'byCases' tactic failed, unexpected new hypothesis");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_byCases_toByCasesSubgoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_byCases_toByCasesSubgoal___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_byCases_toByCasesSubgoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
x_13 = l_Lean_Meta_byCases_toByCasesSubgoal___closed__2;
x_14 = l_Lean_throwError___at_Lean_Meta_byCases_toByCasesSubgoal___spec__1(x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fget(x_9, x_15);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_8);
x_20 = l_Lean_Meta_byCases_toByCasesSubgoal___closed__2;
x_21 = l_Lean_throwError___at_Lean_Meta_byCases_toByCasesSubgoal___spec__1(x_20, x_2, x_3, x_4, x_5, x_6);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases_toByCasesSubgoal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_byCases_toByCasesSubgoal___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_byCases_toByCasesSubgoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_byCases_toByCasesSubgoal(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
static lean_object* _init_l_Lean_Meta_byCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hByCases");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_byCases___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_byCases___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_byCases___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_byCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'byCases' tactic failed, unexpected number of subgoals");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_byCases___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_byCases___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_byCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_9 = l_Lean_mkNot(x_2);
lean_inc(x_2);
x_10 = l_Lean_mkOr(x_2, x_9);
x_11 = l_Lean_mkEM(x_2);
x_12 = l_Lean_Meta_byCases___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_assert(x_1, x_12, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
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
x_26 = l_Lean_Meta_byCases___closed__3;
lean_inc(x_25);
x_27 = lean_array_push(x_26, x_25);
x_28 = lean_array_push(x_27, x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Meta_Cases_cases(x_22, x_21, x_28, x_4, x_5, x_6, x_7, x_19);
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
x_35 = l_Lean_Meta_byCases___closed__5;
x_36 = l_Lean_throwError___at_Lean_Meta_byCases___spec__1(x_35, x_4, x_5, x_6, x_7, x_31);
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
x_41 = l_Lean_Meta_byCases_toByCasesSubgoal(x_38, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_byCases_toByCasesSubgoal(x_40, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_67 = l_Lean_Meta_byCases___closed__3;
lean_inc(x_66);
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_array_push(x_68, x_66);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Lean_Meta_Cases_cases(x_63, x_62, x_69, x_4, x_5, x_6, x_7, x_19);
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
x_76 = l_Lean_Meta_byCases___closed__5;
x_77 = l_Lean_throwError___at_Lean_Meta_byCases___spec__1(x_76, x_4, x_5, x_6, x_7, x_72);
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
x_82 = l_Lean_Meta_byCases_toByCasesSubgoal(x_79, x_4, x_5, x_6, x_7, x_72);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_byCases_toByCasesSubgoal(x_81, x_4, x_5, x_6, x_7, x_84);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_byCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_byCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3624_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Cases_cases___lambda__2___closed__9;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Induction(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Injection(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Induction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(lean_io_mk_world());
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
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3);
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
l_Lean_Meta_generalizeIndices___lambda__1___closed__1 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__1);
l_Lean_Meta_generalizeIndices___lambda__1___closed__2 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___closed__1);
l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1 = _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__1);
l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__2 = _init_l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__2();
lean_mark_persistent(l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1);
l_Lean_Meta_Cases_unifyEqs_substEq___closed__1 = _init_l_Lean_Meta_Cases_unifyEqs_substEq___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs_substEq___closed__1);
l_Lean_Meta_Cases_unifyEqs_substEq___closed__2 = _init_l_Lean_Meta_Cases_unifyEqs_substEq___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs_substEq___closed__2);
l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__1 = _init_l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__1);
l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__2 = _init_l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs___lambda__1___closed__2);
l_Lean_Meta_Cases_unifyEqs_injection___closed__1 = _init_l_Lean_Meta_Cases_unifyEqs_injection___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs_injection___closed__1);
l_Lean_Meta_Cases_unifyEqs_injection___closed__2 = _init_l_Lean_Meta_Cases_unifyEqs_injection___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_unifyEqs_injection___closed__2);
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
l_Lean_Meta_Cases_cases___lambda__2___closed__11 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__11);
l_Lean_Meta_Cases_cases___closed__1 = _init_l_Lean_Meta_Cases_cases___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___closed__1);
l_Lean_Meta_casesRec___lambda__1___closed__1 = _init_l_Lean_Meta_casesRec___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_casesRec___lambda__1___closed__1);
l_Lean_Meta_casesAnd___lambda__1___closed__1 = _init_l_Lean_Meta_casesAnd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_casesAnd___lambda__1___closed__1);
l_Lean_Meta_casesAnd___lambda__1___closed__2 = _init_l_Lean_Meta_casesAnd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_casesAnd___lambda__1___closed__2);
l_Lean_Meta_casesAnd___closed__1 = _init_l_Lean_Meta_casesAnd___closed__1();
lean_mark_persistent(l_Lean_Meta_casesAnd___closed__1);
l_Lean_Meta_casesAnd___closed__2 = _init_l_Lean_Meta_casesAnd___closed__2();
lean_mark_persistent(l_Lean_Meta_casesAnd___closed__2);
l_Lean_Meta_casesAnd___closed__3 = _init_l_Lean_Meta_casesAnd___closed__3();
lean_mark_persistent(l_Lean_Meta_casesAnd___closed__3);
l_Lean_Meta_casesAnd___closed__4 = _init_l_Lean_Meta_casesAnd___closed__4();
lean_mark_persistent(l_Lean_Meta_casesAnd___closed__4);
l_Lean_Meta_substEqs___closed__1 = _init_l_Lean_Meta_substEqs___closed__1();
lean_mark_persistent(l_Lean_Meta_substEqs___closed__1);
l_Lean_Meta_byCases_toByCasesSubgoal___closed__1 = _init_l_Lean_Meta_byCases_toByCasesSubgoal___closed__1();
lean_mark_persistent(l_Lean_Meta_byCases_toByCasesSubgoal___closed__1);
l_Lean_Meta_byCases_toByCasesSubgoal___closed__2 = _init_l_Lean_Meta_byCases_toByCasesSubgoal___closed__2();
lean_mark_persistent(l_Lean_Meta_byCases_toByCasesSubgoal___closed__2);
l_Lean_Meta_byCases___closed__1 = _init_l_Lean_Meta_byCases___closed__1();
lean_mark_persistent(l_Lean_Meta_byCases___closed__1);
l_Lean_Meta_byCases___closed__2 = _init_l_Lean_Meta_byCases___closed__2();
lean_mark_persistent(l_Lean_Meta_byCases___closed__2);
l_Lean_Meta_byCases___closed__3 = _init_l_Lean_Meta_byCases___closed__3();
lean_mark_persistent(l_Lean_Meta_byCases___closed__3);
l_Lean_Meta_byCases___closed__4 = _init_l_Lean_Meta_byCases___closed__4();
lean_mark_persistent(l_Lean_Meta_byCases___closed__4);
l_Lean_Meta_byCases___closed__5 = _init_l_Lean_Meta_byCases___closed__5();
lean_mark_persistent(l_Lean_Meta_byCases___closed__5);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_3624_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
