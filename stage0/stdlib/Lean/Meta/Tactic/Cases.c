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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2;
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1;
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__3(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7;
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5;
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__3;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
extern lean_object* l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__4___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5(lean_object*, size_t, size_t, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__5;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_casesOnSuffix;
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__6___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore___rarg___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__2;
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__1;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__1(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__3(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__1;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__1;
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_generalizeIndices_match__2(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__4;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_2324_(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_Context_nminors___default___boxed(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__5(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Meta_Cases_Context_nminors___default(lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__4(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__5___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__4;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs_match__1(lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5;
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Cases_cases_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop_match__1(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2;
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__1;
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1;
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1;
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__2(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__6(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_indentExpr(x_1);
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_24 = l_Lean_Expr_getAppArgs___closed__1;
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
x_42 = l_Lean_Expr_getAppArgs___closed__1;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_10);
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
x_14 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_9, x_3, x_4, x_5, x_6, x_13);
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
x_17 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_9, x_12, x_3, x_4, x_5, x_6, x_16);
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
x_24 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_23);
x_25 = l_Lean_mkConst(x_24, x_23);
lean_inc(x_1);
lean_inc(x_9);
x_26 = l_Lean_mkApp4(x_25, x_9, x_1, x_12, x_2);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
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
x_34 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_33);
x_35 = l_Lean_mkConst(x_34, x_33);
lean_inc(x_1);
lean_inc(x_9);
x_36 = l_Lean_mkApp4(x_35, x_9, x_1, x_12, x_2);
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
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
x_46 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_45);
x_47 = l_Lean_mkConst(x_46, x_45);
lean_inc(x_1);
lean_inc(x_9);
x_48 = l_Lean_mkApp3(x_47, x_9, x_1, x_2);
x_49 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
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
x_56 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_55);
x_57 = l_Lean_mkConst(x_56, x_55);
lean_inc(x_1);
lean_inc(x_9);
x_58 = l_Lean_mkApp3(x_57, x_9, x_1, x_2);
x_59 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = lean_array_push(x_2, x_8);
x_17 = lean_array_push(x_3, x_4);
x_18 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l_Lean_Expr_Lean_Expr___instance__11;
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
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_6);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_1);
lean_closure_set(x_23, 5, x_2);
lean_closure_set(x_23, 6, x_3);
x_24 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2;
x_25 = 0;
x_26 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_24, x_25, x_21, x_23, x_7, x_8, x_9, x_10, x_20);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg(x_1, x_2, x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_generalizeIndices_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_generalizeIndices_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_generalizeIndices_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_generalizeIndices_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_generalizeIndices_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_generalizeIndices_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_16);
x_23 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(x_16, x_18, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_mkOptionalNode___closed__2;
x_27 = lean_array_push(x_26, x_3);
lean_inc(x_11);
x_28 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(x_27, x_24, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_4);
x_31 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(x_4, x_29, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 2;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___spec__2(x_5, x_6, x_32, x_34, x_21, x_35, x_11, x_12, x_13, x_14, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_37);
x_39 = l_Lean_mkAppN(x_37, x_7);
x_40 = l_Lean_mkApp(x_39, x_8);
x_41 = l_Lean_mkAppN(x_40, x_9);
x_42 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_2, x_41, x_11, x_12, x_13, x_14, x_38);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Expr_mvarId_x21(x_37);
lean_dec(x_37);
x_45 = lean_array_get_size(x_4);
lean_dec(x_4);
x_46 = lean_box(0);
x_47 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_48 = l_Lean_Meta_introNCore(x_44, x_45, x_46, x_47, x_11, x_12, x_13, x_14, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_Meta_intro1Core(x_52, x_47, x_11, x_12, x_13, x_14, x_50);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_array_get_size(x_16);
lean_dec(x_16);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_53, 0, x_59);
return x_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_array_get_size(x_16);
lean_dec(x_16);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_51);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_51);
lean_dec(x_16);
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
return x_53;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_53, 0);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_71 = !lean_is_exclusive(x_48);
if (x_71 == 0)
{
return x_48;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_48, 0);
x_73 = lean_ctor_get(x_48, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_48);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_31);
if (x_75 == 0)
{
return x_31;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_31, 0);
x_77 = lean_ctor_get(x_31, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_31);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_28);
if (x_79 == 0)
{
return x_28;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_28, 0);
x_81 = lean_ctor_get(x_28, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_28);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_23);
if (x_83 == 0)
{
return x_23;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_23, 0);
x_85 = lean_ctor_get(x_23, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_23);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_20);
if (x_87 == 0)
{
return x_20;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_20, 0);
x_89 = lean_ctor_get(x_20, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_20);
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
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_17);
if (x_91 == 0)
{
return x_17;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_17, 0);
x_93 = lean_ctor_get(x_17, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_17);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_23 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2;
x_24 = 0;
x_25 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_23, x_24, x_19, x_22, x_10, x_11, x_12, x_13, x_18);
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_14 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs___rarg(x_6, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
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
x_18 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_15, x_17, x_14, x_16, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_22 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_21, x_9, x_10, x_11, x_12, x_13);
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
x_26 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_23, x_25, x_9, x_10, x_11, x_12, x_24);
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
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
lean_dec(x_11);
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
x_1 = lean_mk_string("indexed inductive type expected");
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
x_21 = lean_box(0);
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_20, x_21, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_29 = lean_box(0);
x_30 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_28, x_29, x_9, x_10, x_11, x_12, x_17);
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
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
x_38 = lean_box(0);
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_37, x_38, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
x_46 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
x_47 = lean_box(0);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_46, x_47, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___spec__1(x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_4);
x_15 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_2, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_18, x_4, x_5, x_6, x_7, x_17);
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
x_24 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(x_1, x_3, x_10, x_12, x_16, x_20, x_25, x_27, x_4, x_5, x_6, x_7, x_21);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_7);
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
lean_dec(x_7);
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
lean_dec(x_7);
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
lean_object* l_Lean_Meta_generalizeIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lambda__1), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarWithIdCore___rarg___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_7);
return x_16;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
lean_object* l_Lean_Meta_Cases_Context_nminors___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___rarg(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_Cases_Context_nminors___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Cases_Context_nminors___default(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Cases_Context_majorTypeIndices___default(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_28 = l_Lean_Meta_casesOnSuffix___closed__1;
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
x_37 = l_List_lengthAux___rarg(x_35, x_36);
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
x_46 = l_List_lengthAux___rarg(x_44, x_45);
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
x_70 = l_Lean_Meta_casesOnSuffix___closed__1;
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
x_80 = l_List_lengthAux___rarg(x_78, x_79);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_Expr_eq_x3f___closed__2;
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
x_15 = l_Lean_Expr_heq_x3f___closed__2;
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
x_18 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_10);
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
x_22 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_21, x_2, x_3, x_4, x_5, x_20);
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
x_27 = l_Lean_Expr_getAppArgs___closed__1;
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
x_43 = l_Lean_Expr_eq_x3f___closed__2;
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
x_47 = l_Lean_Expr_heq_x3f___closed__2;
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
x_51 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_41);
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
x_55 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_54, x_2, x_3, x_4, x_5, x_53);
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
x_60 = l_Lean_Expr_getAppArgs___closed__1;
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
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_4, x_5);
x_9 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
x_5 = x_11;
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
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
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = 0;
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_3, x_15, x_22, x_23);
return x_24;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_3, x_7, x_14, x_15);
return x_16;
}
}
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_dec(x_4);
if (x_3 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_nat_dec_le(x_2, x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_2);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_10, x_1, x_15, x_16);
lean_dec(x_10);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_inc(x_24);
lean_inc(x_4);
x_25 = lean_metavar_ctx_get_expr_assignment(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Lean_MetavarContext_getDecl(x_4, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_3, x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_32, x_6);
return x_33;
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_4);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_34, x_39);
return x_41;
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_inc(x_48);
lean_dec(x_5);
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_47, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_5, 2);
lean_inc(x_59);
lean_dec(x_5);
lean_inc(x_4);
x_60 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_58, x_6);
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
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
lean_dec(x_5);
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_69, x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_70, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_dec(x_5);
x_90 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_89, x_6);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_5, 2);
lean_inc(x_91);
lean_dec(x_5);
x_92 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4, x_91, x_6);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_4, x_5);
x_9 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
x_5 = x_11;
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
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
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = 0;
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_3, x_15, x_22, x_23);
return x_24;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_3, x_7, x_14, x_15);
return x_16;
}
}
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_dec(x_4);
if (x_3 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_nat_dec_le(x_2, x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_2);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_10, x_1, x_15, x_16);
lean_dec(x_10);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_inc(x_24);
lean_inc(x_4);
x_25 = lean_metavar_ctx_get_expr_assignment(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Lean_MetavarContext_getDecl(x_4, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_3, x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_32, x_6);
return x_33;
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_4);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_34, x_39);
return x_41;
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_inc(x_48);
lean_dec(x_5);
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_47, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_5, 2);
lean_inc(x_59);
lean_dec(x_5);
lean_inc(x_4);
x_60 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_58, x_6);
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
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
lean_dec(x_5);
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_69, x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_70, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_dec(x_5);
x_90 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_89, x_6);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_5, 2);
lean_inc(x_91);
lean_dec(x_5);
x_92 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_91, x_6);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_4, x_5);
x_9 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
x_5 = x_11;
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
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
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = 0;
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_3, x_15, x_22, x_23);
return x_24;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_3, x_7, x_14, x_15);
return x_16;
}
}
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_dec(x_4);
if (x_3 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_nat_dec_le(x_2, x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_2);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_10, x_1, x_15, x_16);
lean_dec(x_10);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_inc(x_24);
lean_inc(x_4);
x_25 = lean_metavar_ctx_get_expr_assignment(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Lean_MetavarContext_getDecl(x_4, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_3, x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_32, x_6);
return x_33;
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_4);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_34, x_39);
return x_41;
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_inc(x_48);
lean_dec(x_5);
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_47, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_5, 2);
lean_inc(x_59);
lean_dec(x_5);
lean_inc(x_4);
x_60 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_58, x_6);
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
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
lean_dec(x_5);
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_69, x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_70, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_dec(x_5);
x_90 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_89, x_6);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_5, 2);
lean_inc(x_91);
lean_dec(x_5);
x_92 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_91, x_6);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_4, x_5);
x_9 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
x_5 = x_11;
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
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
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = 0;
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_3, x_15, x_22, x_23);
return x_24;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_3, x_7, x_14, x_15);
return x_16;
}
}
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_dec(x_4);
if (x_3 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_nat_dec_le(x_2, x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_2);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_10, x_1, x_15, x_16);
lean_dec(x_10);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_inc(x_24);
lean_inc(x_4);
x_25 = lean_metavar_ctx_get_expr_assignment(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Lean_MetavarContext_getDecl(x_4, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_3, x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_32, x_6);
return x_33;
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_4);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_34, x_39);
return x_41;
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_inc(x_48);
lean_dec(x_5);
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_47, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_5, 2);
lean_inc(x_59);
lean_dec(x_5);
lean_inc(x_4);
x_60 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_58, x_6);
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
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
lean_dec(x_5);
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_69, x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_70, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_dec(x_5);
x_90 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_89, x_6);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_5, 2);
lean_inc(x_91);
lean_dec(x_5);
x_92 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_91, x_6);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_4, x_5);
x_9 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
x_5 = x_11;
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
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
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = 0;
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(x_1, x_2, x_3, x_15, x_22, x_23);
return x_24;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_3, x_7, x_14, x_15);
return x_16;
}
}
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_dec(x_4);
if (x_3 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_nat_dec_le(x_2, x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_2);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_10, x_1, x_15, x_16);
lean_dec(x_10);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_inc(x_24);
lean_inc(x_4);
x_25 = lean_metavar_ctx_get_expr_assignment(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Lean_MetavarContext_getDecl(x_4, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_3, x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_32, x_6);
return x_33;
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_4);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_34, x_39);
return x_41;
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_inc(x_48);
lean_dec(x_5);
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_47, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_5, 2);
lean_inc(x_59);
lean_dec(x_5);
lean_inc(x_4);
x_60 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_58, x_6);
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
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
lean_dec(x_5);
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_69, x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_70, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_dec(x_5);
x_90 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_89, x_6);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_5, 2);
lean_inc(x_91);
lean_dec(x_5);
x_92 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_91, x_6);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_4, x_5);
x_9 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
x_5 = x_11;
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
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
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_5, x_12, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = 0;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
x_21 = 0;
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(x_1, x_2, x_3, x_15, x_22, x_23);
return x_24;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_5 + x_9;
x_5 = x_10;
goto _start;
}
else
{
if (x_3 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_LocalDecl_fvarId(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_14);
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_2);
x_19 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_14, x_1, x_17, x_18);
lean_dec(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; 
x_21 = 1;
x_22 = x_5 + x_21;
x_5 = x_22;
goto _start;
}
}
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(x_1, x_2, x_3, x_7, x_14, x_15);
return x_16;
}
}
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_dec(x_4);
if (x_3 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_nat_dec_le(x_2, x_2);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_2);
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_10, x_1, x_15, x_16);
lean_dec(x_10);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
lean_inc(x_24);
lean_inc(x_4);
x_25 = lean_metavar_ctx_get_expr_assignment(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = l_Lean_MetavarContext_getDecl(x_4, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_3, x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_32, x_6);
return x_33;
}
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_4);
x_36 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_34, x_39);
return x_41;
}
else
{
x_5 = x_34;
x_6 = x_39;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_inc(x_48);
lean_dec(x_5);
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_47, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_48, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_48);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_5, 2);
lean_inc(x_59);
lean_dec(x_5);
lean_inc(x_4);
x_60 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_58, x_6);
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
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_59, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_59);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 8:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
lean_dec(x_5);
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_69, x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_70, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_71, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_71);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 0);
lean_dec(x_82);
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_72, 0);
lean_dec(x_86);
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_dec(x_5);
x_90 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_89, x_6);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_5, 2);
lean_inc(x_91);
lean_dec(x_5);
x_92 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4, x_91, x_6);
return x_92;
}
default: 
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7) {
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
lean_dec(x_9);
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7) {
_start:
{
uint8_t x_8; uint8_t x_14; 
x_14 = x_6 == x_7;
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_uget(x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = 0;
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_fvarId(x_17);
x_19 = lean_ctor_get(x_1, 3);
x_20 = l_Lean_LocalDecl_fvarId(x_19);
x_21 = lean_name_eq(x_18, x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_3);
if (x_23 == 0)
{
lean_dec(x_18);
if (x_21 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_17, 3);
lean_inc(x_78);
lean_dec(x_17);
x_79 = 0;
x_24 = x_79;
x_25 = x_78;
goto block_44;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_17, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_17, 4);
lean_inc(x_81);
lean_dec(x_17);
x_82 = 0;
x_45 = x_82;
x_46 = x_80;
x_47 = x_81;
goto block_77;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_17, 3);
lean_inc(x_83);
lean_dec(x_17);
x_84 = 1;
x_24 = x_84;
x_25 = x_83;
goto block_44;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_17, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_17, 4);
lean_inc(x_86);
lean_dec(x_17);
x_87 = 1;
x_45 = x_87;
x_46 = x_85;
x_47 = x_86;
goto block_77;
}
}
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_3, x_3);
if (x_88 == 0)
{
lean_dec(x_18);
if (x_21 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_17, 3);
lean_inc(x_89);
lean_dec(x_17);
x_90 = 0;
x_24 = x_90;
x_25 = x_89;
goto block_44;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_17, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_17, 4);
lean_inc(x_92);
lean_dec(x_17);
x_93 = 0;
x_45 = x_93;
x_46 = x_91;
x_47 = x_92;
goto block_77;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_17, 3);
lean_inc(x_94);
lean_dec(x_17);
x_95 = 1;
x_24 = x_95;
x_25 = x_94;
goto block_44;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_17, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_17, 4);
lean_inc(x_97);
lean_dec(x_17);
x_98 = 1;
x_45 = x_98;
x_46 = x_96;
x_47 = x_97;
goto block_77;
}
}
}
else
{
if (x_21 == 0)
{
size_t x_99; size_t x_100; uint8_t x_101; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_3);
x_101 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_18, x_2, x_99, x_100);
lean_dec(x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_17, 3);
lean_inc(x_102);
lean_dec(x_17);
x_24 = x_101;
x_25 = x_102;
goto block_44;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_17, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_17, 4);
lean_inc(x_104);
lean_dec(x_17);
x_45 = x_101;
x_46 = x_103;
x_47 = x_104;
goto block_77;
}
}
else
{
lean_dec(x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_17, 3);
lean_inc(x_105);
lean_dec(x_17);
x_106 = 1;
x_24 = x_106;
x_25 = x_105;
goto block_44;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_17, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_17, 4);
lean_inc(x_108);
lean_dec(x_17);
x_109 = 1;
x_45 = x_109;
x_46 = x_107;
x_47 = x_108;
goto block_77;
}
}
}
}
block_44:
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasFVar(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
lean_dec(x_25);
if (x_24 == 0)
{
uint8_t x_28; 
x_28 = 1;
x_8 = x_28;
goto block_13;
}
else
{
uint8_t x_29; 
x_29 = 0;
x_8 = x_29;
goto block_13;
}
}
else
{
if (x_24 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_31 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_2, x_3, x_23, x_4, x_25, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 1;
x_8 = x_34;
goto block_13;
}
else
{
uint8_t x_35; 
x_35 = 0;
x_8 = x_35;
goto block_13;
}
}
else
{
uint8_t x_36; 
lean_dec(x_25);
x_36 = 0;
x_8 = x_36;
goto block_13;
}
}
}
else
{
if (x_24 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_38 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_2, x_3, x_23, x_4, x_25, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 1;
x_8 = x_41;
goto block_13;
}
else
{
uint8_t x_42; 
x_42 = 0;
x_8 = x_42;
goto block_13;
}
}
else
{
uint8_t x_43; 
lean_dec(x_25);
x_43 = 0;
x_8 = x_43;
goto block_13;
}
}
}
block_77:
{
lean_object* x_48; uint8_t x_70; 
x_70 = l_Lean_Expr_hasFVar(x_46);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Expr_hasMVar(x_46);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_46);
x_72 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_48 = x_72;
goto block_69;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_74 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_2, x_3, x_23, x_4, x_46, x_73);
x_48 = x_74;
goto block_69;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_2, x_3, x_23, x_4, x_46, x_75);
x_48 = x_76;
goto block_69;
}
block_69:
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_Expr_hasFVar(x_47);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Expr_hasMVar(x_47);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_47);
if (x_45 == 0)
{
uint8_t x_54; 
x_54 = 1;
x_8 = x_54;
goto block_13;
}
else
{
uint8_t x_55; 
x_55 = 0;
x_8 = x_55;
goto block_13;
}
}
else
{
if (x_45 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_4);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_2, x_3, x_23, x_4, x_47, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = 1;
x_8 = x_59;
goto block_13;
}
else
{
uint8_t x_60; 
x_60 = 0;
x_8 = x_60;
goto block_13;
}
}
else
{
uint8_t x_61; 
lean_dec(x_51);
lean_dec(x_47);
x_61 = 0;
x_8 = x_61;
goto block_13;
}
}
}
else
{
if (x_45 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_inc(x_4);
x_62 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_2, x_3, x_23, x_4, x_47, x_51);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = 1;
x_8 = x_65;
goto block_13;
}
else
{
uint8_t x_66; 
x_66 = 0;
x_8 = x_66;
goto block_13;
}
}
else
{
uint8_t x_67; 
lean_dec(x_51);
lean_dec(x_47);
x_67 = 0;
x_8 = x_67;
goto block_13;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_48);
lean_dec(x_47);
x_68 = 0;
x_8 = x_68;
goto block_13;
}
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_4);
x_110 = 0;
return x_110;
}
block_13:
{
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_6 + x_9;
x_6 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = 1;
return x_12;
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
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
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_17);
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
return x_25;
}
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7) {
_start:
{
uint8_t x_8; uint8_t x_14; 
x_14 = x_6 == x_7;
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_uget(x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = 0;
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_fvarId(x_17);
x_19 = lean_ctor_get(x_1, 3);
x_20 = l_Lean_LocalDecl_fvarId(x_19);
x_21 = lean_name_eq(x_18, x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_3);
if (x_23 == 0)
{
lean_dec(x_18);
if (x_21 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_17, 3);
lean_inc(x_78);
lean_dec(x_17);
x_79 = 0;
x_24 = x_79;
x_25 = x_78;
goto block_44;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_17, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_17, 4);
lean_inc(x_81);
lean_dec(x_17);
x_82 = 0;
x_45 = x_82;
x_46 = x_80;
x_47 = x_81;
goto block_77;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_17, 3);
lean_inc(x_83);
lean_dec(x_17);
x_84 = 1;
x_24 = x_84;
x_25 = x_83;
goto block_44;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_17, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_17, 4);
lean_inc(x_86);
lean_dec(x_17);
x_87 = 1;
x_45 = x_87;
x_46 = x_85;
x_47 = x_86;
goto block_77;
}
}
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_3, x_3);
if (x_88 == 0)
{
lean_dec(x_18);
if (x_21 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_17, 3);
lean_inc(x_89);
lean_dec(x_17);
x_90 = 0;
x_24 = x_90;
x_25 = x_89;
goto block_44;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_17, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_17, 4);
lean_inc(x_92);
lean_dec(x_17);
x_93 = 0;
x_45 = x_93;
x_46 = x_91;
x_47 = x_92;
goto block_77;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_17, 3);
lean_inc(x_94);
lean_dec(x_17);
x_95 = 1;
x_24 = x_95;
x_25 = x_94;
goto block_44;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_17, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_17, 4);
lean_inc(x_97);
lean_dec(x_17);
x_98 = 1;
x_45 = x_98;
x_46 = x_96;
x_47 = x_97;
goto block_77;
}
}
}
else
{
if (x_21 == 0)
{
size_t x_99; size_t x_100; uint8_t x_101; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_3);
x_101 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_18, x_2, x_99, x_100);
lean_dec(x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_17, 3);
lean_inc(x_102);
lean_dec(x_17);
x_24 = x_101;
x_25 = x_102;
goto block_44;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_17, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_17, 4);
lean_inc(x_104);
lean_dec(x_17);
x_45 = x_101;
x_46 = x_103;
x_47 = x_104;
goto block_77;
}
}
else
{
lean_dec(x_18);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_17, 3);
lean_inc(x_105);
lean_dec(x_17);
x_106 = 1;
x_24 = x_106;
x_25 = x_105;
goto block_44;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_17, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_17, 4);
lean_inc(x_108);
lean_dec(x_17);
x_109 = 1;
x_45 = x_109;
x_46 = x_107;
x_47 = x_108;
goto block_77;
}
}
}
}
block_44:
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasFVar(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
lean_dec(x_25);
if (x_24 == 0)
{
uint8_t x_28; 
x_28 = 1;
x_8 = x_28;
goto block_13;
}
else
{
uint8_t x_29; 
x_29 = 0;
x_8 = x_29;
goto block_13;
}
}
else
{
if (x_24 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_31 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_2, x_3, x_23, x_4, x_25, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 1;
x_8 = x_34;
goto block_13;
}
else
{
uint8_t x_35; 
x_35 = 0;
x_8 = x_35;
goto block_13;
}
}
else
{
uint8_t x_36; 
lean_dec(x_25);
x_36 = 0;
x_8 = x_36;
goto block_13;
}
}
}
else
{
if (x_24 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_38 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_2, x_3, x_23, x_4, x_25, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = 1;
x_8 = x_41;
goto block_13;
}
else
{
uint8_t x_42; 
x_42 = 0;
x_8 = x_42;
goto block_13;
}
}
else
{
uint8_t x_43; 
lean_dec(x_25);
x_43 = 0;
x_8 = x_43;
goto block_13;
}
}
}
block_77:
{
lean_object* x_48; uint8_t x_70; 
x_70 = l_Lean_Expr_hasFVar(x_46);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Expr_hasMVar(x_46);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_46);
x_72 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_48 = x_72;
goto block_69;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_74 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_2, x_3, x_23, x_4, x_46, x_73);
x_48 = x_74;
goto block_69;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_76 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_2, x_3, x_23, x_4, x_46, x_75);
x_48 = x_76;
goto block_69;
}
block_69:
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_Expr_hasFVar(x_47);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Expr_hasMVar(x_47);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_47);
if (x_45 == 0)
{
uint8_t x_54; 
x_54 = 1;
x_8 = x_54;
goto block_13;
}
else
{
uint8_t x_55; 
x_55 = 0;
x_8 = x_55;
goto block_13;
}
}
else
{
if (x_45 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_4);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_2, x_3, x_23, x_4, x_47, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = 1;
x_8 = x_59;
goto block_13;
}
else
{
uint8_t x_60; 
x_60 = 0;
x_8 = x_60;
goto block_13;
}
}
else
{
uint8_t x_61; 
lean_dec(x_51);
lean_dec(x_47);
x_61 = 0;
x_8 = x_61;
goto block_13;
}
}
}
else
{
if (x_45 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_inc(x_4);
x_62 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_2, x_3, x_23, x_4, x_47, x_51);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = 1;
x_8 = x_65;
goto block_13;
}
else
{
uint8_t x_66; 
x_66 = 0;
x_8 = x_66;
goto block_13;
}
}
else
{
uint8_t x_67; 
lean_dec(x_51);
lean_dec(x_47);
x_67 = 0;
x_8 = x_67;
goto block_13;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_48);
lean_dec(x_47);
x_68 = 0;
x_8 = x_68;
goto block_13;
}
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_4);
x_110 = 0;
return x_110;
}
block_13:
{
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_6 + x_9;
x_6 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = 1;
return x_12;
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_4);
x_7 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
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
return x_17;
}
}
}
else
{
lean_dec(x_4);
return x_7;
}
}
}
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_Expr_Lean_Expr___instance__11;
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
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_Expr_Lean_Expr___instance__11;
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
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(lean_object* x_1, size_t x_2, size_t x_3) {
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
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_Lean_Expr_Lean_Expr___instance__11;
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
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 6);
x_8 = l_Array_isEmpty___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_34; uint8_t x_35; 
x_9 = lean_array_get_size(x_7);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_9);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_9);
x_36 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(x_7, x_9, x_9);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_10 = x_37;
goto block_33;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_9, x_9);
if (x_41 == 0)
{
uint8_t x_42; 
lean_inc(x_9);
x_42 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53(x_7, x_9, x_9);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_10 = x_43;
goto block_33;
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
else
{
size_t x_47; size_t x_48; uint8_t x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_9);
x_49 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54(x_7, x_47, x_48);
if (x_49 == 0)
{
uint8_t x_50; 
lean_inc(x_9);
x_50 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56(x_7, x_9, x_9);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_10 = x_51;
goto block_33;
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_9);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_6);
return x_54;
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_9);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_6);
return x_57;
}
}
}
block_33:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_st_ref_get(x_3, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_11, 1);
x_17 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_7, x_9, x_15, x_16);
lean_dec(x_9);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_11, 1);
x_26 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_7, x_9, x_24, x_25);
lean_dec(x_9);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
}
}
}
else
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_6);
return x_60;
}
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(x_1, x_2, x_7, x_4, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_10);
return x_11;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__53___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__54___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__56___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = x_2 == x_3;
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_uget(x_1, x_2);
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
lean_inc(x_17);
x_24 = l_Lean_Meta_FVarSubst_get(x_23, x_17);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_8, x_9);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_6, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Meta_clear(x_21, x_25, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_33);
lean_dec(x_29);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_4, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_4, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_17, x_23);
lean_dec(x_17);
lean_ctor_set(x_18, 2, x_40);
lean_ctor_set(x_18, 0, x_38);
x_10 = x_4;
x_11 = x_39;
goto block_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_17, x_23);
lean_dec(x_17);
lean_ctor_set(x_18, 2, x_43);
lean_ctor_set(x_18, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_18);
lean_ctor_set(x_44, 1, x_19);
x_10 = x_44;
x_11 = x_42;
goto block_15;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_18);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_29, x_5, x_6, x_7, x_8, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_33, x_5, x_6, x_7, x_8, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_10 = x_4;
x_11 = x_49;
goto block_15;
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
lean_dec(x_17);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
x_52 = lean_ctor_get(x_18, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
lean_inc(x_17);
x_53 = l_Lean_Meta_FVarSubst_get(x_52, x_17);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_8, x_9);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_6, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_63 = l_Lean_Meta_clear(x_50, x_54, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_58);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_64 = x_4;
} else {
 lean_dec_ref(x_4);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_17, x_52);
lean_dec(x_17);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_51);
lean_ctor_set(x_68, 2, x_67);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_19);
x_10 = x_69;
x_11 = x_66;
goto block_15;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_19);
lean_dec(x_17);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_58, x_5, x_6, x_7, x_8, x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_62, x_5, x_6, x_7, x_8, x_72);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_10 = x_4;
x_11 = x_74;
goto block_15;
}
}
else
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_19);
lean_dec(x_17);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_4);
lean_ctor_set(x_75, 1, x_9);
return x_75;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = x_2 + x_12;
x_2 = x_13;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l_Lean_Init_LeanInit___instance__1;
x_17 = lean_array_get(x_16, x_2, x_8);
lean_inc(x_4);
lean_inc(x_17);
x_18 = l_Lean_mkConst(x_17, x_4);
x_19 = l_Lean_mkAppN(x_18, x_5);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 2);
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
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapIdxM_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_11 = lean_box_uint64(x_8);
x_12 = lean_box_uint64(x_10);
x_13 = lean_apply_4(x_3, x_7, x_11, x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_3(x_4, x_14, x_16, x_2);
return x_17;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_3(x_5, x_1, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_5);
x_22 = lean_apply_2(x_6, x_1, x_2);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__3___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_2, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_4(x_2, x_9, x_10, x_11, x_12);
return x_13;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__6___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cases");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_LocalDecl_type(x_7);
x_14 = l_Lean_Expr_heq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Expr_isAppOfArity(x_13, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_Expr_eq_x3f___closed__2;
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_13, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5;
x_22 = lean_box(0);
x_23 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_1, x_21, x_22, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Expr_appFn_x21(x_13);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_26);
lean_inc(x_25);
x_27 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_25, x_26, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_25);
x_31 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_25, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_26);
x_34 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_26, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_expr_eqv(x_32, x_25);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_2);
x_38 = l_Lean_mkFVar(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_32, x_35, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_LocalDecl_userName(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_43 = l_Lean_Meta_assert(x_1, x_42, x_40, x_38, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_46 = l_Lean_Meta_clear(x_44, x_2, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_3, x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_51, 2, x_5);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
x_53 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_50, x_52, x_8, x_9, x_10, x_11, x_48);
lean_dec(x_50);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_43);
if (x_58 == 0)
{
return x_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_43, 0);
x_60 = lean_ctor_get(x_43, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_43);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_39);
if (x_62 == 0)
{
return x_39;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_39, 0);
x_64 = lean_ctor_get(x_39, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_39);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
x_66 = lean_expr_eqv(x_35, x_26);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_2);
x_67 = l_Lean_mkFVar(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_32, x_35, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_LocalDecl_userName(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_72 = l_Lean_Meta_assert(x_1, x_71, x_69, x_67, x_8, x_9, x_10, x_11, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_75 = l_Lean_Meta_clear(x_73, x_2, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_3, x_78);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_4);
lean_ctor_set(x_80, 2, x_5);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_6);
x_82 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_79, x_81, x_8, x_9, x_10, x_11, x_77);
lean_dec(x_79);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
return x_75;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
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
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_68);
if (x_91 == 0)
{
return x_68;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_68, 0);
x_93 = lean_ctor_get(x_68, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_68);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_32);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_95; lean_object* x_96; 
lean_dec(x_26);
x_95 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_96 = l_Lean_Meta_substCore(x_1, x_2, x_95, x_5, x_95, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_array_get_size(x_4);
x_102 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_103 = 0;
x_104 = x_4;
x_105 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1(x_99, x_102, x_103, x_104);
x_106 = x_105;
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_99);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_6);
x_109 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_108, x_8, x_9, x_10, x_11, x_98);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_96);
if (x_110 == 0)
{
return x_96;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_96, 0);
x_112 = lean_ctor_get(x_96, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_96);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_114 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = !lean_is_exclusive(x_114);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_114, 0);
lean_dec(x_117);
x_118 = lean_box(0);
lean_ctor_set(x_114, 0, x_118);
return x_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_dec(x_114);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
lean_dec(x_114);
x_123 = lean_ctor_get(x_115, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
lean_dec(x_115);
x_125 = lean_nat_add(x_3, x_124);
lean_dec(x_124);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_4);
lean_ctor_set(x_126, 2, x_5);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_6);
x_128 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_125, x_127, x_8, x_9, x_10, x_11, x_122);
lean_dec(x_125);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_129 = !lean_is_exclusive(x_114);
if (x_129 == 0)
{
return x_114;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_114, 0);
x_131 = lean_ctor_get(x_114, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_114);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
case 1:
{
switch (lean_obj_tag(x_26)) {
case 0:
{
uint8_t x_133; uint8_t x_134; lean_object* x_135; 
lean_dec(x_26);
lean_dec(x_25);
x_133 = 0;
x_134 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_135 = l_Lean_Meta_substCore(x_1, x_2, x_133, x_5, x_134, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; size_t x_141; size_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_array_get_size(x_4);
x_141 = lean_usize_of_nat(x_140);
lean_dec(x_140);
x_142 = 0;
x_143 = x_4;
x_144 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2(x_138, x_141, x_142, x_143);
x_145 = x_144;
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_138);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_6);
x_148 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_147, x_8, x_9, x_10, x_11, x_137);
return x_148;
}
else
{
uint8_t x_149; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_135);
if (x_149 == 0)
{
return x_135;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_135, 0);
x_151 = lean_ctor_get(x_135, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_135);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 1:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_25, 0);
lean_inc(x_153);
lean_dec(x_25);
x_154 = lean_ctor_get(x_26, 0);
lean_inc(x_154);
lean_dec(x_26);
lean_inc(x_8);
x_155 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_153, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_8);
x_158 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_154, x_8, x_9, x_10, x_11, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_LocalDecl_index(x_156);
lean_dec(x_156);
x_162 = l_Lean_LocalDecl_index(x_159);
lean_dec(x_159);
x_163 = lean_nat_dec_lt(x_161, x_162);
lean_dec(x_162);
lean_dec(x_161);
x_164 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_165 = l_Lean_Meta_substCore(x_1, x_2, x_163, x_5, x_164, x_8, x_9, x_10, x_11, x_160);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_array_get_size(x_4);
x_171 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_172 = 0;
x_173 = x_4;
x_174 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3(x_168, x_171, x_172, x_173);
x_175 = x_174;
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_169);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_168);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_6);
x_178 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_177, x_8, x_9, x_10, x_11, x_167);
return x_178;
}
else
{
uint8_t x_179; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_179 = !lean_is_exclusive(x_165);
if (x_179 == 0)
{
return x_165;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_165, 0);
x_181 = lean_ctor_get(x_165, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_165);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_156);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_158);
if (x_183 == 0)
{
return x_158;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_158, 0);
x_185 = lean_ctor_get(x_158, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_158);
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
lean_dec(x_154);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_155);
if (x_187 == 0)
{
return x_155;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_155, 0);
x_189 = lean_ctor_get(x_155, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_155);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
case 2:
{
uint8_t x_191; uint8_t x_192; lean_object* x_193; 
lean_dec(x_26);
lean_dec(x_25);
x_191 = 0;
x_192 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_193 = l_Lean_Meta_substCore(x_1, x_2, x_191, x_5, x_192, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; size_t x_199; size_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_198 = lean_array_get_size(x_4);
x_199 = lean_usize_of_nat(x_198);
lean_dec(x_198);
x_200 = 0;
x_201 = x_4;
x_202 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4(x_196, x_199, x_200, x_201);
x_203 = x_202;
x_204 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_204, 2, x_196);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_6);
x_206 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_205, x_8, x_9, x_10, x_11, x_195);
return x_206;
}
else
{
uint8_t x_207; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_207 = !lean_is_exclusive(x_193);
if (x_207 == 0)
{
return x_193;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_193, 0);
x_209 = lean_ctor_get(x_193, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_193);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
case 3:
{
uint8_t x_211; uint8_t x_212; lean_object* x_213; 
lean_dec(x_26);
lean_dec(x_25);
x_211 = 0;
x_212 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_213 = l_Lean_Meta_substCore(x_1, x_2, x_211, x_5, x_212, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_array_get_size(x_4);
x_219 = lean_usize_of_nat(x_218);
lean_dec(x_218);
x_220 = 0;
x_221 = x_4;
x_222 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5(x_216, x_219, x_220, x_221);
x_223 = x_222;
x_224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_224, 0, x_217);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_224, 2, x_216);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_6);
x_226 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_225, x_8, x_9, x_10, x_11, x_215);
return x_226;
}
else
{
uint8_t x_227; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_227 = !lean_is_exclusive(x_213);
if (x_227 == 0)
{
return x_213;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_213, 0);
x_229 = lean_ctor_get(x_213, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_213);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
case 4:
{
uint8_t x_231; uint8_t x_232; lean_object* x_233; 
lean_dec(x_26);
lean_dec(x_25);
x_231 = 0;
x_232 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_233 = l_Lean_Meta_substCore(x_1, x_2, x_231, x_5, x_232, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; size_t x_239; size_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_array_get_size(x_4);
x_239 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_240 = 0;
x_241 = x_4;
x_242 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6(x_236, x_239, x_240, x_241);
x_243 = x_242;
x_244 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_244, 0, x_237);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_244, 2, x_236);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_6);
x_246 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_245, x_8, x_9, x_10, x_11, x_235);
return x_246;
}
else
{
uint8_t x_247; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_247 = !lean_is_exclusive(x_233);
if (x_247 == 0)
{
return x_233;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_233, 0);
x_249 = lean_ctor_get(x_233, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_233);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
case 5:
{
uint8_t x_251; uint8_t x_252; lean_object* x_253; 
lean_dec(x_26);
lean_dec(x_25);
x_251 = 0;
x_252 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_253 = l_Lean_Meta_substCore(x_1, x_2, x_251, x_5, x_252, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; size_t x_259; size_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_array_get_size(x_4);
x_259 = lean_usize_of_nat(x_258);
lean_dec(x_258);
x_260 = 0;
x_261 = x_4;
x_262 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7(x_256, x_259, x_260, x_261);
x_263 = x_262;
x_264 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_256);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_6);
x_266 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_265, x_8, x_9, x_10, x_11, x_255);
return x_266;
}
else
{
uint8_t x_267; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_267 = !lean_is_exclusive(x_253);
if (x_267 == 0)
{
return x_253;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_253, 0);
x_269 = lean_ctor_get(x_253, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_253);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
case 6:
{
uint8_t x_271; uint8_t x_272; lean_object* x_273; 
lean_dec(x_26);
lean_dec(x_25);
x_271 = 0;
x_272 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_273 = l_Lean_Meta_substCore(x_1, x_2, x_271, x_5, x_272, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; size_t x_279; size_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
lean_dec(x_274);
x_278 = lean_array_get_size(x_4);
x_279 = lean_usize_of_nat(x_278);
lean_dec(x_278);
x_280 = 0;
x_281 = x_4;
x_282 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8(x_276, x_279, x_280, x_281);
x_283 = x_282;
x_284 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_276);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_6);
x_286 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_285, x_8, x_9, x_10, x_11, x_275);
return x_286;
}
else
{
uint8_t x_287; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_287 = !lean_is_exclusive(x_273);
if (x_287 == 0)
{
return x_273;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_273, 0);
x_289 = lean_ctor_get(x_273, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_273);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
case 7:
{
uint8_t x_291; uint8_t x_292; lean_object* x_293; 
lean_dec(x_26);
lean_dec(x_25);
x_291 = 0;
x_292 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_293 = l_Lean_Meta_substCore(x_1, x_2, x_291, x_5, x_292, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; size_t x_299; size_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_ctor_get(x_294, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_array_get_size(x_4);
x_299 = lean_usize_of_nat(x_298);
lean_dec(x_298);
x_300 = 0;
x_301 = x_4;
x_302 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9(x_296, x_299, x_300, x_301);
x_303 = x_302;
x_304 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_304, 0, x_297);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_304, 2, x_296);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_6);
x_306 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_305, x_8, x_9, x_10, x_11, x_295);
return x_306;
}
else
{
uint8_t x_307; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_307 = !lean_is_exclusive(x_293);
if (x_307 == 0)
{
return x_293;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_293, 0);
x_309 = lean_ctor_get(x_293, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_293);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
case 8:
{
uint8_t x_311; uint8_t x_312; lean_object* x_313; 
lean_dec(x_26);
lean_dec(x_25);
x_311 = 0;
x_312 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_313 = l_Lean_Meta_substCore(x_1, x_2, x_311, x_5, x_312, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; size_t x_319; size_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get(x_314, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_array_get_size(x_4);
x_319 = lean_usize_of_nat(x_318);
lean_dec(x_318);
x_320 = 0;
x_321 = x_4;
x_322 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10(x_316, x_319, x_320, x_321);
x_323 = x_322;
x_324 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_324, 0, x_317);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set(x_324, 2, x_316);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_6);
x_326 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_325, x_8, x_9, x_10, x_11, x_315);
return x_326;
}
else
{
uint8_t x_327; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_327 = !lean_is_exclusive(x_313);
if (x_327 == 0)
{
return x_313;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_313, 0);
x_329 = lean_ctor_get(x_313, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_313);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
case 9:
{
uint8_t x_331; uint8_t x_332; lean_object* x_333; 
lean_dec(x_26);
lean_dec(x_25);
x_331 = 0;
x_332 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_333 = l_Lean_Meta_substCore(x_1, x_2, x_331, x_5, x_332, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; size_t x_339; size_t x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_ctor_get(x_334, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_array_get_size(x_4);
x_339 = lean_usize_of_nat(x_338);
lean_dec(x_338);
x_340 = 0;
x_341 = x_4;
x_342 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11(x_336, x_339, x_340, x_341);
x_343 = x_342;
x_344 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_344, 0, x_337);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_344, 2, x_336);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_6);
x_346 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_345, x_8, x_9, x_10, x_11, x_335);
return x_346;
}
else
{
uint8_t x_347; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_347 = !lean_is_exclusive(x_333);
if (x_347 == 0)
{
return x_333;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_333, 0);
x_349 = lean_ctor_get(x_333, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_333);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
case 10:
{
uint8_t x_351; uint8_t x_352; lean_object* x_353; 
lean_dec(x_26);
lean_dec(x_25);
x_351 = 0;
x_352 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_353 = l_Lean_Meta_substCore(x_1, x_2, x_351, x_5, x_352, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; size_t x_359; size_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
x_358 = lean_array_get_size(x_4);
x_359 = lean_usize_of_nat(x_358);
lean_dec(x_358);
x_360 = 0;
x_361 = x_4;
x_362 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12(x_356, x_359, x_360, x_361);
x_363 = x_362;
x_364 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_364, 0, x_357);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set(x_364, 2, x_356);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_6);
x_366 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_365, x_8, x_9, x_10, x_11, x_355);
return x_366;
}
else
{
uint8_t x_367; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_367 = !lean_is_exclusive(x_353);
if (x_367 == 0)
{
return x_353;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_353, 0);
x_369 = lean_ctor_get(x_353, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_353);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
default: 
{
uint8_t x_371; uint8_t x_372; lean_object* x_373; 
lean_dec(x_26);
lean_dec(x_25);
x_371 = 0;
x_372 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_373 = l_Lean_Meta_substCore(x_1, x_2, x_371, x_5, x_372, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; size_t x_379; size_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_374, 1);
lean_inc(x_377);
lean_dec(x_374);
x_378 = lean_array_get_size(x_4);
x_379 = lean_usize_of_nat(x_378);
lean_dec(x_378);
x_380 = 0;
x_381 = x_4;
x_382 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13(x_376, x_379, x_380, x_381);
x_383 = x_382;
x_384 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_384, 0, x_377);
lean_ctor_set(x_384, 1, x_383);
lean_ctor_set(x_384, 2, x_376);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_6);
x_386 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_385, x_8, x_9, x_10, x_11, x_375);
return x_386;
}
else
{
uint8_t x_387; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_387 = !lean_is_exclusive(x_373);
if (x_387 == 0)
{
return x_373;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_373, 0);
x_389 = lean_ctor_get(x_373, 1);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_373);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
return x_390;
}
}
}
}
}
case 2:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_391; lean_object* x_392; 
lean_dec(x_26);
x_391 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_392 = l_Lean_Meta_substCore(x_1, x_2, x_391, x_5, x_391, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; size_t x_398; size_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_ctor_get(x_393, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_393, 1);
lean_inc(x_396);
lean_dec(x_393);
x_397 = lean_array_get_size(x_4);
x_398 = lean_usize_of_nat(x_397);
lean_dec(x_397);
x_399 = 0;
x_400 = x_4;
x_401 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14(x_395, x_398, x_399, x_400);
x_402 = x_401;
x_403 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_403, 0, x_396);
lean_ctor_set(x_403, 1, x_402);
lean_ctor_set(x_403, 2, x_395);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_6);
x_405 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_404, x_8, x_9, x_10, x_11, x_394);
return x_405;
}
else
{
uint8_t x_406; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_406 = !lean_is_exclusive(x_392);
if (x_406 == 0)
{
return x_392;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_392, 0);
x_408 = lean_ctor_get(x_392, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_392);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
lean_object* x_410; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_410 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
if (lean_obj_tag(x_411) == 0)
{
uint8_t x_412; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_412 = !lean_is_exclusive(x_410);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_410, 0);
lean_dec(x_413);
x_414 = lean_box(0);
lean_ctor_set(x_410, 0, x_414);
return x_410;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_410, 1);
lean_inc(x_415);
lean_dec(x_410);
x_416 = lean_box(0);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_410, 1);
lean_inc(x_418);
lean_dec(x_410);
x_419 = lean_ctor_get(x_411, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_411, 1);
lean_inc(x_420);
lean_dec(x_411);
x_421 = lean_nat_add(x_3, x_420);
lean_dec(x_420);
x_422 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_4);
lean_ctor_set(x_422, 2, x_5);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_6);
x_424 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_421, x_423, x_8, x_9, x_10, x_11, x_418);
lean_dec(x_421);
return x_424;
}
}
else
{
uint8_t x_425; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_425 = !lean_is_exclusive(x_410);
if (x_425 == 0)
{
return x_410;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_410, 0);
x_427 = lean_ctor_get(x_410, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_410);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
}
case 3:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_429; lean_object* x_430; 
lean_dec(x_26);
x_429 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_430 = l_Lean_Meta_substCore(x_1, x_2, x_429, x_5, x_429, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; size_t x_436; size_t x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_ctor_get(x_431, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
x_435 = lean_array_get_size(x_4);
x_436 = lean_usize_of_nat(x_435);
lean_dec(x_435);
x_437 = 0;
x_438 = x_4;
x_439 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15(x_433, x_436, x_437, x_438);
x_440 = x_439;
x_441 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_441, 0, x_434);
lean_ctor_set(x_441, 1, x_440);
lean_ctor_set(x_441, 2, x_433);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_6);
x_443 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_442, x_8, x_9, x_10, x_11, x_432);
return x_443;
}
else
{
uint8_t x_444; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_444 = !lean_is_exclusive(x_430);
if (x_444 == 0)
{
return x_430;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_430, 0);
x_446 = lean_ctor_get(x_430, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_430);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
else
{
lean_object* x_448; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_448 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
if (lean_obj_tag(x_449) == 0)
{
uint8_t x_450; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_450 = !lean_is_exclusive(x_448);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_448, 0);
lean_dec(x_451);
x_452 = lean_box(0);
lean_ctor_set(x_448, 0, x_452);
return x_448;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_448, 1);
lean_inc(x_453);
lean_dec(x_448);
x_454 = lean_box(0);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_453);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_456 = lean_ctor_get(x_448, 1);
lean_inc(x_456);
lean_dec(x_448);
x_457 = lean_ctor_get(x_449, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_449, 1);
lean_inc(x_458);
lean_dec(x_449);
x_459 = lean_nat_add(x_3, x_458);
lean_dec(x_458);
x_460 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_460, 0, x_457);
lean_ctor_set(x_460, 1, x_4);
lean_ctor_set(x_460, 2, x_5);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_6);
x_462 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_459, x_461, x_8, x_9, x_10, x_11, x_456);
lean_dec(x_459);
return x_462;
}
}
else
{
uint8_t x_463; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_463 = !lean_is_exclusive(x_448);
if (x_463 == 0)
{
return x_448;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_448, 0);
x_465 = lean_ctor_get(x_448, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_448);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
case 4:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_467; lean_object* x_468; 
lean_dec(x_26);
x_467 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_468 = l_Lean_Meta_substCore(x_1, x_2, x_467, x_5, x_467, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; size_t x_474; size_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_469, 1);
lean_inc(x_472);
lean_dec(x_469);
x_473 = lean_array_get_size(x_4);
x_474 = lean_usize_of_nat(x_473);
lean_dec(x_473);
x_475 = 0;
x_476 = x_4;
x_477 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16(x_471, x_474, x_475, x_476);
x_478 = x_477;
x_479 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_479, 0, x_472);
lean_ctor_set(x_479, 1, x_478);
lean_ctor_set(x_479, 2, x_471);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_6);
x_481 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_480, x_8, x_9, x_10, x_11, x_470);
return x_481;
}
else
{
uint8_t x_482; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_482 = !lean_is_exclusive(x_468);
if (x_482 == 0)
{
return x_468;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_468, 0);
x_484 = lean_ctor_get(x_468, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_468);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
else
{
lean_object* x_486; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_486 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
if (lean_obj_tag(x_487) == 0)
{
uint8_t x_488; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_488 = !lean_is_exclusive(x_486);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_486, 0);
lean_dec(x_489);
x_490 = lean_box(0);
lean_ctor_set(x_486, 0, x_490);
return x_486;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_486, 1);
lean_inc(x_491);
lean_dec(x_486);
x_492 = lean_box(0);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_494 = lean_ctor_get(x_486, 1);
lean_inc(x_494);
lean_dec(x_486);
x_495 = lean_ctor_get(x_487, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_487, 1);
lean_inc(x_496);
lean_dec(x_487);
x_497 = lean_nat_add(x_3, x_496);
lean_dec(x_496);
x_498 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_4);
lean_ctor_set(x_498, 2, x_5);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_6);
x_500 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_497, x_499, x_8, x_9, x_10, x_11, x_494);
lean_dec(x_497);
return x_500;
}
}
else
{
uint8_t x_501; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_501 = !lean_is_exclusive(x_486);
if (x_501 == 0)
{
return x_486;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_486, 0);
x_503 = lean_ctor_get(x_486, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_486);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
}
case 5:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_505; lean_object* x_506; 
lean_dec(x_26);
x_505 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_506 = l_Lean_Meta_substCore(x_1, x_2, x_505, x_5, x_505, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; size_t x_512; size_t x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_ctor_get(x_507, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_507, 1);
lean_inc(x_510);
lean_dec(x_507);
x_511 = lean_array_get_size(x_4);
x_512 = lean_usize_of_nat(x_511);
lean_dec(x_511);
x_513 = 0;
x_514 = x_4;
x_515 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17(x_509, x_512, x_513, x_514);
x_516 = x_515;
x_517 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_517, 0, x_510);
lean_ctor_set(x_517, 1, x_516);
lean_ctor_set(x_517, 2, x_509);
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_6);
x_519 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_518, x_8, x_9, x_10, x_11, x_508);
return x_519;
}
else
{
uint8_t x_520; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_520 = !lean_is_exclusive(x_506);
if (x_520 == 0)
{
return x_506;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_506, 0);
x_522 = lean_ctor_get(x_506, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_506);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
else
{
lean_object* x_524; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_524 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
if (lean_obj_tag(x_525) == 0)
{
uint8_t x_526; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_526 = !lean_is_exclusive(x_524);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; 
x_527 = lean_ctor_get(x_524, 0);
lean_dec(x_527);
x_528 = lean_box(0);
lean_ctor_set(x_524, 0, x_528);
return x_524;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_524, 1);
lean_inc(x_529);
lean_dec(x_524);
x_530 = lean_box(0);
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_532 = lean_ctor_get(x_524, 1);
lean_inc(x_532);
lean_dec(x_524);
x_533 = lean_ctor_get(x_525, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_525, 1);
lean_inc(x_534);
lean_dec(x_525);
x_535 = lean_nat_add(x_3, x_534);
lean_dec(x_534);
x_536 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_536, 0, x_533);
lean_ctor_set(x_536, 1, x_4);
lean_ctor_set(x_536, 2, x_5);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_6);
x_538 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_535, x_537, x_8, x_9, x_10, x_11, x_532);
lean_dec(x_535);
return x_538;
}
}
else
{
uint8_t x_539; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_539 = !lean_is_exclusive(x_524);
if (x_539 == 0)
{
return x_524;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_540 = lean_ctor_get(x_524, 0);
x_541 = lean_ctor_get(x_524, 1);
lean_inc(x_541);
lean_inc(x_540);
lean_dec(x_524);
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_541);
return x_542;
}
}
}
}
case 6:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_543; lean_object* x_544; 
lean_dec(x_26);
x_543 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_544 = l_Lean_Meta_substCore(x_1, x_2, x_543, x_5, x_543, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; size_t x_550; size_t x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = lean_ctor_get(x_545, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_545, 1);
lean_inc(x_548);
lean_dec(x_545);
x_549 = lean_array_get_size(x_4);
x_550 = lean_usize_of_nat(x_549);
lean_dec(x_549);
x_551 = 0;
x_552 = x_4;
x_553 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18(x_547, x_550, x_551, x_552);
x_554 = x_553;
x_555 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_555, 0, x_548);
lean_ctor_set(x_555, 1, x_554);
lean_ctor_set(x_555, 2, x_547);
x_556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_6);
x_557 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_556, x_8, x_9, x_10, x_11, x_546);
return x_557;
}
else
{
uint8_t x_558; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_558 = !lean_is_exclusive(x_544);
if (x_558 == 0)
{
return x_544;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_544, 0);
x_560 = lean_ctor_get(x_544, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_544);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
}
else
{
lean_object* x_562; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_562 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
if (lean_obj_tag(x_563) == 0)
{
uint8_t x_564; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_564 = !lean_is_exclusive(x_562);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_562, 0);
lean_dec(x_565);
x_566 = lean_box(0);
lean_ctor_set(x_562, 0, x_566);
return x_562;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_562, 1);
lean_inc(x_567);
lean_dec(x_562);
x_568 = lean_box(0);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_570 = lean_ctor_get(x_562, 1);
lean_inc(x_570);
lean_dec(x_562);
x_571 = lean_ctor_get(x_563, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_563, 1);
lean_inc(x_572);
lean_dec(x_563);
x_573 = lean_nat_add(x_3, x_572);
lean_dec(x_572);
x_574 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_4);
lean_ctor_set(x_574, 2, x_5);
x_575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_6);
x_576 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_573, x_575, x_8, x_9, x_10, x_11, x_570);
lean_dec(x_573);
return x_576;
}
}
else
{
uint8_t x_577; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_577 = !lean_is_exclusive(x_562);
if (x_577 == 0)
{
return x_562;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_562, 0);
x_579 = lean_ctor_get(x_562, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_562);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
}
}
case 7:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_581; lean_object* x_582; 
lean_dec(x_26);
x_581 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_582 = l_Lean_Meta_substCore(x_1, x_2, x_581, x_5, x_581, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; size_t x_588; size_t x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = lean_ctor_get(x_583, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 1);
lean_inc(x_586);
lean_dec(x_583);
x_587 = lean_array_get_size(x_4);
x_588 = lean_usize_of_nat(x_587);
lean_dec(x_587);
x_589 = 0;
x_590 = x_4;
x_591 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19(x_585, x_588, x_589, x_590);
x_592 = x_591;
x_593 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_593, 0, x_586);
lean_ctor_set(x_593, 1, x_592);
lean_ctor_set(x_593, 2, x_585);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_6);
x_595 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_594, x_8, x_9, x_10, x_11, x_584);
return x_595;
}
else
{
uint8_t x_596; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_596 = !lean_is_exclusive(x_582);
if (x_596 == 0)
{
return x_582;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_582, 0);
x_598 = lean_ctor_get(x_582, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_582);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
else
{
lean_object* x_600; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_600 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
if (lean_obj_tag(x_601) == 0)
{
uint8_t x_602; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_602 = !lean_is_exclusive(x_600);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; 
x_603 = lean_ctor_get(x_600, 0);
lean_dec(x_603);
x_604 = lean_box(0);
lean_ctor_set(x_600, 0, x_604);
return x_600;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_ctor_get(x_600, 1);
lean_inc(x_605);
lean_dec(x_600);
x_606 = lean_box(0);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_608 = lean_ctor_get(x_600, 1);
lean_inc(x_608);
lean_dec(x_600);
x_609 = lean_ctor_get(x_601, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_601, 1);
lean_inc(x_610);
lean_dec(x_601);
x_611 = lean_nat_add(x_3, x_610);
lean_dec(x_610);
x_612 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_4);
lean_ctor_set(x_612, 2, x_5);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_6);
x_614 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_611, x_613, x_8, x_9, x_10, x_11, x_608);
lean_dec(x_611);
return x_614;
}
}
else
{
uint8_t x_615; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_615 = !lean_is_exclusive(x_600);
if (x_615 == 0)
{
return x_600;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_600, 0);
x_617 = lean_ctor_get(x_600, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_600);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_616);
lean_ctor_set(x_618, 1, x_617);
return x_618;
}
}
}
}
case 8:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_619; lean_object* x_620; 
lean_dec(x_26);
x_619 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_620 = l_Lean_Meta_substCore(x_1, x_2, x_619, x_5, x_619, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; size_t x_626; size_t x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = lean_ctor_get(x_621, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_621, 1);
lean_inc(x_624);
lean_dec(x_621);
x_625 = lean_array_get_size(x_4);
x_626 = lean_usize_of_nat(x_625);
lean_dec(x_625);
x_627 = 0;
x_628 = x_4;
x_629 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20(x_623, x_626, x_627, x_628);
x_630 = x_629;
x_631 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_631, 0, x_624);
lean_ctor_set(x_631, 1, x_630);
lean_ctor_set(x_631, 2, x_623);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_6);
x_633 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_632, x_8, x_9, x_10, x_11, x_622);
return x_633;
}
else
{
uint8_t x_634; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_634 = !lean_is_exclusive(x_620);
if (x_634 == 0)
{
return x_620;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_620, 0);
x_636 = lean_ctor_get(x_620, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_620);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
else
{
lean_object* x_638; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_638 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
if (lean_obj_tag(x_639) == 0)
{
uint8_t x_640; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_640 = !lean_is_exclusive(x_638);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; 
x_641 = lean_ctor_get(x_638, 0);
lean_dec(x_641);
x_642 = lean_box(0);
lean_ctor_set(x_638, 0, x_642);
return x_638;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_638, 1);
lean_inc(x_643);
lean_dec(x_638);
x_644 = lean_box(0);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_643);
return x_645;
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_646 = lean_ctor_get(x_638, 1);
lean_inc(x_646);
lean_dec(x_638);
x_647 = lean_ctor_get(x_639, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_639, 1);
lean_inc(x_648);
lean_dec(x_639);
x_649 = lean_nat_add(x_3, x_648);
lean_dec(x_648);
x_650 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_650, 0, x_647);
lean_ctor_set(x_650, 1, x_4);
lean_ctor_set(x_650, 2, x_5);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_6);
x_652 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_649, x_651, x_8, x_9, x_10, x_11, x_646);
lean_dec(x_649);
return x_652;
}
}
else
{
uint8_t x_653; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_653 = !lean_is_exclusive(x_638);
if (x_653 == 0)
{
return x_638;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_638, 0);
x_655 = lean_ctor_get(x_638, 1);
lean_inc(x_655);
lean_inc(x_654);
lean_dec(x_638);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
}
}
}
case 9:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_657; lean_object* x_658; 
lean_dec(x_26);
x_657 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_658 = l_Lean_Meta_substCore(x_1, x_2, x_657, x_5, x_657, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; size_t x_664; size_t x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
x_661 = lean_ctor_get(x_659, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_659, 1);
lean_inc(x_662);
lean_dec(x_659);
x_663 = lean_array_get_size(x_4);
x_664 = lean_usize_of_nat(x_663);
lean_dec(x_663);
x_665 = 0;
x_666 = x_4;
x_667 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21(x_661, x_664, x_665, x_666);
x_668 = x_667;
x_669 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_669, 0, x_662);
lean_ctor_set(x_669, 1, x_668);
lean_ctor_set(x_669, 2, x_661);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_6);
x_671 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_670, x_8, x_9, x_10, x_11, x_660);
return x_671;
}
else
{
uint8_t x_672; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_672 = !lean_is_exclusive(x_658);
if (x_672 == 0)
{
return x_658;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_658, 0);
x_674 = lean_ctor_get(x_658, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_658);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
else
{
lean_object* x_676; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_676 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
if (lean_obj_tag(x_677) == 0)
{
uint8_t x_678; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_678 = !lean_is_exclusive(x_676);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_676, 0);
lean_dec(x_679);
x_680 = lean_box(0);
lean_ctor_set(x_676, 0, x_680);
return x_676;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_676, 1);
lean_inc(x_681);
lean_dec(x_676);
x_682 = lean_box(0);
x_683 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_681);
return x_683;
}
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_684 = lean_ctor_get(x_676, 1);
lean_inc(x_684);
lean_dec(x_676);
x_685 = lean_ctor_get(x_677, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_677, 1);
lean_inc(x_686);
lean_dec(x_677);
x_687 = lean_nat_add(x_3, x_686);
lean_dec(x_686);
x_688 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_688, 0, x_685);
lean_ctor_set(x_688, 1, x_4);
lean_ctor_set(x_688, 2, x_5);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_6);
x_690 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_687, x_689, x_8, x_9, x_10, x_11, x_684);
lean_dec(x_687);
return x_690;
}
}
else
{
uint8_t x_691; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_691 = !lean_is_exclusive(x_676);
if (x_691 == 0)
{
return x_676;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_692 = lean_ctor_get(x_676, 0);
x_693 = lean_ctor_get(x_676, 1);
lean_inc(x_693);
lean_inc(x_692);
lean_dec(x_676);
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_692);
lean_ctor_set(x_694, 1, x_693);
return x_694;
}
}
}
}
case 10:
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_695; lean_object* x_696; 
lean_dec(x_26);
x_695 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_696 = l_Lean_Meta_substCore(x_1, x_2, x_695, x_5, x_695, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; size_t x_702; size_t x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_ctor_get(x_697, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_697, 1);
lean_inc(x_700);
lean_dec(x_697);
x_701 = lean_array_get_size(x_4);
x_702 = lean_usize_of_nat(x_701);
lean_dec(x_701);
x_703 = 0;
x_704 = x_4;
x_705 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22(x_699, x_702, x_703, x_704);
x_706 = x_705;
x_707 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_707, 0, x_700);
lean_ctor_set(x_707, 1, x_706);
lean_ctor_set(x_707, 2, x_699);
x_708 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_6);
x_709 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_708, x_8, x_9, x_10, x_11, x_698);
return x_709;
}
else
{
uint8_t x_710; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_710 = !lean_is_exclusive(x_696);
if (x_710 == 0)
{
return x_696;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_696, 0);
x_712 = lean_ctor_get(x_696, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_696);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_711);
lean_ctor_set(x_713, 1, x_712);
return x_713;
}
}
}
else
{
lean_object* x_714; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_714 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; 
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
if (lean_obj_tag(x_715) == 0)
{
uint8_t x_716; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_716 = !lean_is_exclusive(x_714);
if (x_716 == 0)
{
lean_object* x_717; lean_object* x_718; 
x_717 = lean_ctor_get(x_714, 0);
lean_dec(x_717);
x_718 = lean_box(0);
lean_ctor_set(x_714, 0, x_718);
return x_714;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_714, 1);
lean_inc(x_719);
lean_dec(x_714);
x_720 = lean_box(0);
x_721 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_721, 0, x_720);
lean_ctor_set(x_721, 1, x_719);
return x_721;
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_722 = lean_ctor_get(x_714, 1);
lean_inc(x_722);
lean_dec(x_714);
x_723 = lean_ctor_get(x_715, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_715, 1);
lean_inc(x_724);
lean_dec(x_715);
x_725 = lean_nat_add(x_3, x_724);
lean_dec(x_724);
x_726 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_726, 0, x_723);
lean_ctor_set(x_726, 1, x_4);
lean_ctor_set(x_726, 2, x_5);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_6);
x_728 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_725, x_727, x_8, x_9, x_10, x_11, x_722);
lean_dec(x_725);
return x_728;
}
}
else
{
uint8_t x_729; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_729 = !lean_is_exclusive(x_714);
if (x_729 == 0)
{
return x_714;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_714, 0);
x_731 = lean_ctor_get(x_714, 1);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_714);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
}
}
default: 
{
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_733; lean_object* x_734; 
lean_dec(x_26);
x_733 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_734 = l_Lean_Meta_substCore(x_1, x_2, x_733, x_5, x_733, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; size_t x_740; size_t x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_ctor_get(x_735, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_735, 1);
lean_inc(x_738);
lean_dec(x_735);
x_739 = lean_array_get_size(x_4);
x_740 = lean_usize_of_nat(x_739);
lean_dec(x_739);
x_741 = 0;
x_742 = x_4;
x_743 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23(x_737, x_740, x_741, x_742);
x_744 = x_743;
x_745 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_745, 0, x_738);
lean_ctor_set(x_745, 1, x_744);
lean_ctor_set(x_745, 2, x_737);
x_746 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_6);
x_747 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_746, x_8, x_9, x_10, x_11, x_736);
return x_747;
}
else
{
uint8_t x_748; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_748 = !lean_is_exclusive(x_734);
if (x_748 == 0)
{
return x_734;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_734, 0);
x_750 = lean_ctor_get(x_734, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_734);
x_751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
return x_751;
}
}
}
else
{
lean_object* x_752; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_752 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
if (lean_obj_tag(x_753) == 0)
{
uint8_t x_754; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_754 = !lean_is_exclusive(x_752);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_752, 0);
lean_dec(x_755);
x_756 = lean_box(0);
lean_ctor_set(x_752, 0, x_756);
return x_752;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_752, 1);
lean_inc(x_757);
lean_dec(x_752);
x_758 = lean_box(0);
x_759 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
return x_759;
}
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_760 = lean_ctor_get(x_752, 1);
lean_inc(x_760);
lean_dec(x_752);
x_761 = lean_ctor_get(x_753, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_753, 1);
lean_inc(x_762);
lean_dec(x_753);
x_763 = lean_nat_add(x_3, x_762);
lean_dec(x_762);
x_764 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_4);
lean_ctor_set(x_764, 2, x_5);
x_765 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_6);
x_766 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_763, x_765, x_8, x_9, x_10, x_11, x_760);
lean_dec(x_763);
return x_766;
}
}
else
{
uint8_t x_767; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_767 = !lean_is_exclusive(x_752);
if (x_767 == 0)
{
return x_752;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_752, 0);
x_769 = lean_ctor_get(x_752, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_752);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
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
uint8_t x_771; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_771 = !lean_is_exclusive(x_34);
if (x_771 == 0)
{
return x_34;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_34, 0);
x_773 = lean_ctor_get(x_34, 1);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_34);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
return x_774;
}
}
}
else
{
uint8_t x_775; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_775 = !lean_is_exclusive(x_31);
if (x_775 == 0)
{
return x_31;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_776 = lean_ctor_get(x_31, 0);
x_777 = lean_ctor_get(x_31, 1);
lean_inc(x_777);
lean_inc(x_776);
lean_dec(x_31);
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_776);
lean_ctor_set(x_778, 1, x_777);
return x_778;
}
}
}
else
{
lean_object* x_779; lean_object* x_780; 
lean_dec(x_26);
lean_dec(x_25);
x_779 = lean_ctor_get(x_27, 1);
lean_inc(x_779);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_780 = l_Lean_Meta_clear(x_1, x_2, x_8, x_9, x_10, x_11, x_779);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_783 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_783, 0, x_781);
lean_ctor_set(x_783, 1, x_4);
lean_ctor_set(x_783, 2, x_5);
x_784 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set(x_784, 1, x_6);
x_785 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_784, x_8, x_9, x_10, x_11, x_782);
return x_785;
}
else
{
uint8_t x_786; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_786 = !lean_is_exclusive(x_780);
if (x_786 == 0)
{
return x_780;
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = lean_ctor_get(x_780, 0);
x_788 = lean_ctor_get(x_780, 1);
lean_inc(x_788);
lean_inc(x_787);
lean_dec(x_780);
x_789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_788);
return x_789;
}
}
}
}
else
{
uint8_t x_790; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_790 = !lean_is_exclusive(x_27);
if (x_790 == 0)
{
return x_27;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_27, 0);
x_792 = lean_ctor_get(x_27, 1);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_27);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
return x_793;
}
}
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_794 = l_Lean_Expr_appFn_x21(x_13);
x_795 = l_Lean_Expr_appFn_x21(x_794);
lean_dec(x_794);
x_796 = l_Lean_Expr_appArg_x21(x_795);
lean_dec(x_795);
x_797 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
lean_inc(x_2);
x_798 = l_Lean_mkFVar(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_799 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp(x_798, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
lean_dec(x_799);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_802 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_796, x_797, x_8, x_9, x_10, x_11, x_801);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec(x_802);
x_805 = l_Lean_LocalDecl_userName(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_806 = l_Lean_Meta_assert(x_1, x_805, x_803, x_800, x_8, x_9, x_10, x_11, x_804);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
lean_dec(x_806);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_809 = l_Lean_Meta_clear(x_807, x_2, x_8, x_9, x_10, x_11, x_808);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
lean_dec(x_809);
x_812 = lean_unsigned_to_nat(1u);
x_813 = lean_nat_add(x_3, x_812);
x_814 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_814, 0, x_810);
lean_ctor_set(x_814, 1, x_4);
lean_ctor_set(x_814, 2, x_5);
x_815 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_6);
x_816 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_813, x_815, x_8, x_9, x_10, x_11, x_811);
lean_dec(x_813);
return x_816;
}
else
{
uint8_t x_817; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_817 = !lean_is_exclusive(x_809);
if (x_817 == 0)
{
return x_809;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_809, 0);
x_819 = lean_ctor_get(x_809, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_809);
x_820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
return x_820;
}
}
}
else
{
uint8_t x_821; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_821 = !lean_is_exclusive(x_806);
if (x_821 == 0)
{
return x_806;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_806, 0);
x_823 = lean_ctor_get(x_806, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_806);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
else
{
uint8_t x_825; 
lean_dec(x_800);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_825 = !lean_is_exclusive(x_802);
if (x_825 == 0)
{
return x_802;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_802, 0);
x_827 = lean_ctor_get(x_802, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_802);
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_826);
lean_ctor_set(x_828, 1, x_827);
return x_828;
}
}
}
else
{
uint8_t x_829; 
lean_dec(x_797);
lean_dec(x_796);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_829 = !lean_is_exclusive(x_799);
if (x_829 == 0)
{
return x_799;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_830 = lean_ctor_get(x_799, 0);
x_831 = lean_ctor_get(x_799, 1);
lean_inc(x_831);
lean_inc(x_830);
lean_dec(x_799);
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
return x_832;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__1;
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs [");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_33; lean_object* x_34; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_1, x_10);
x_52 = lean_st_ref_get(x_6, x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 3);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = 0;
x_33 = x_57;
x_34 = x_56;
goto block_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_60 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_59, x_3, x_4, x_5, x_6, x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_33 = x_63;
x_34 = x_62;
goto block_51;
}
block_32:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
lean_dec(x_13);
x_18 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Meta_intro1Core(x_15, x_18, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_24, 0, x_22);
lean_inc(x_23);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___boxed), 12, 6);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_11);
lean_closure_set(x_25, 3, x_16);
lean_closure_set(x_25, 4, x_17);
lean_closure_set(x_25, 5, x_14);
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_23, x_26, x_3, x_4, x_5, x_6, x_21);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
block_51:
{
if (x_33 == 0)
{
x_12 = x_34;
goto block_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_nat_add(x_11, x_10);
x_36 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_49 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_48, x_47, x_3, x_4, x_5, x_6, x_34);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_12 = x_50;
goto block_32;
}
}
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_st_ref_get(x_6, x_7);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 3);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = 0;
x_64 = x_89;
x_65 = x_88;
goto block_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_91 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_92 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_91, x_3, x_4, x_5, x_6, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_unbox(x_93);
lean_dec(x_93);
x_64 = x_95;
x_65 = x_94;
goto block_83;
}
block_83:
{
if (x_64 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_2);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_76 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_75, x_74, x_3, x_4, x_5, x_6, x_65);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_2);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_3 + x_16;
x_3 = x_17;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_array_push(x_5, x_20);
x_22 = 1;
x_23 = x_3 + x_22;
x_3 = x_23;
x_5 = x_21;
x_10 = x_19;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Array_empty___closed__1;
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
x_14 = l_Array_empty___closed__1;
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
x_18 = l_Array_empty___closed__1;
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(x_1, x_2, x_16, x_17, x_18, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_getInductiveUniverseAndParams(x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Meta_casesOnSuffix;
x_21 = lean_name_mk_string(x_19, x_20);
x_22 = lean_ctor_get(x_17, 4);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_List_redLength___rarg(x_22);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean_dec(x_23);
x_25 = l_List_toArrayAux___rarg(x_22, x_24);
lean_inc(x_3);
x_26 = l_Lean_Meta_induction(x_2, x_3, x_21, x_4, x_5, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_28, x_25, x_3, x_15, x_16);
lean_dec(x_16);
lean_dec(x_25);
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
x_32 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_30, x_25, x_3, x_15, x_16);
lean_dec(x_16);
lean_dec(x_25);
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
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_11 = l_Lean_mkFVar(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_box(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed), 11, 5);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_Cases_cases_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_Cases_cases_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not applicable to the given hypothesis");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after generalizeIndices\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Cases_cases___lambda__1___closed__3;
x_16 = lean_box(0);
x_17 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_15, x_16, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Meta_generalizeIndices(x_3, x_1, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_74 = lean_st_ref_get(x_10, x_26);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 3);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get_uint8(x_76, sizeof(void*)*1);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = 0;
x_27 = x_79;
x_28 = x_78;
goto block_73;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_82 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_81, x_7, x_8, x_9, x_10, x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_27 = x_85;
x_28 = x_84;
goto block_73;
}
block_73:
{
if (x_27 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 2);
lean_inc(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_29, x_30, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
x_34 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_25, x_32, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_25, 3);
lean_inc(x_37);
lean_dec(x_25);
x_38 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(x_37, x_35, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_35);
lean_dec(x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
else
{
uint8_t x_43; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_25, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_25, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_25, 3);
lean_inc(x_49);
lean_inc(x_47);
x_50 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_51 = l_Lean_Meta_Cases_cases___lambda__1___closed__5;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_56 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_55, x_54, x_7, x_8, x_9, x_10, x_28);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_58 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_47, x_48, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_61 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_25, x_59, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(x_49, x_62, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_62);
lean_dec(x_49);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_49);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_49);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_58);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_24);
if (x_86 == 0)
{
return x_24;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_24, 0);
x_88 = lean_ctor_get(x_24, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_24);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
x_90 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_3, x_1, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_18);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_12);
if (x_91 == 0)
{
return x_12;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_12, 0);
x_93 = lean_ctor_get(x_12, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_12);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_box(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__1___boxed), 11, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_Cases_cases___lambda__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_cases(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_2324_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
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
lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object* w) {
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
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2);
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
l_Lean_Meta_generalizeIndices___lambda__1___closed__1 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__1);
l_Lean_Meta_generalizeIndices___lambda__1___closed__2 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___boxed__const__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__2);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__4);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__6 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__6);
l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7 = _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7);
l_Lean_Meta_Cases_cases___lambda__1___closed__1 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__1);
l_Lean_Meta_Cases_cases___lambda__1___closed__2 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__2);
l_Lean_Meta_Cases_cases___lambda__1___closed__3 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__3);
l_Lean_Meta_Cases_cases___lambda__1___closed__4 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__4);
l_Lean_Meta_Cases_cases___lambda__1___closed__5 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__5);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_2324_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
