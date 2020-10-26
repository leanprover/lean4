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
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2;
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__1;
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__25(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__2;
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__3(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__24(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7;
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5;
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp___closed__2;
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__3;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_Context_majorTypeIndices___default(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__4___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_match__1(lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_match__1(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__5;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__6___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__2;
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__1;
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__1(lean_object*);
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn_match__1(lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__3(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__1;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkHEqReflImp___closed__1;
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__2(lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__4;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_2418_(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__8;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__2;
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_Context_nminors___default___boxed(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__3;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__5(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Meta_Cases_Context_nminors___default(lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__4(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__4;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs_match__1(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5;
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases_match__1(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop_match__1(lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_mkCasesContext_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__2;
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_withNewIndexEqs_loop___rarg___closed__1;
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__6(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux_match__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__2;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___closed__1;
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_shouldVisit(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_10 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_39 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_7, x_7, x_35, x_37);
x_40 = l_Lean_mkApp(x_39, x_8);
x_41 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_9, x_9, x_35, x_40);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_7, x_7, x_14, x_1);
x_16 = l_Lean_LocalDecl_userName(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_generalizeIndices___spec__1___lambda__3), 12, 6);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_7);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_5);
lean_closure_set(x_17, 5, x_6);
x_18 = 0;
x_19 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_16, x_18, x_15, x_17, x_9, x_10, x_11, x_12, x_13);
return x_19;
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
x_21 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_20, x_20, x_19, x_3);
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
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_3);
x_15 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_2, x_3, x_4, x_5, x_6, x_14);
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
x_19 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_18, x_3, x_4, x_5, x_6, x_17);
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
lean_object* l_Lean_Meta_generalizeIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
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
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_Expr_isFVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
}
}
}
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_9, x_9, x_9);
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
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = 1;
return x_14;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = 1;
return x_14;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_24, x_6);
return x_25;
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
lean_inc(x_4);
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Expr_isApp(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_26, x_31);
return x_33;
}
else
{
x_5 = x_26;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_4);
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_39, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_40, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 7:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 2);
lean_inc(x_51);
lean_dec(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_50, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_51, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 3);
lean_inc(x_63);
lean_dec(x_5);
lean_inc(x_4);
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_65);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_4);
x_68 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_62, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_63, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_63);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_64, 0);
lean_dec(x_78);
return x_64;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
lean_dec(x_5);
x_82 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_81, x_6);
return x_82;
}
case 11:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_5, 2);
lean_inc(x_83);
lean_dec(x_5);
x_84 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_83, x_6);
return x_84;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_24, x_6);
return x_25;
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
lean_inc(x_4);
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Expr_isApp(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_26, x_31);
return x_33;
}
else
{
x_5 = x_26;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_4);
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_39, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_40, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 7:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 2);
lean_inc(x_51);
lean_dec(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_50, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_51, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 3);
lean_inc(x_63);
lean_dec(x_5);
lean_inc(x_4);
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_65);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_4);
x_68 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_62, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_63, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_63);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_64, 0);
lean_dec(x_78);
return x_64;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
lean_dec(x_5);
x_82 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_81, x_6);
return x_82;
}
case 11:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_5, 2);
lean_inc(x_83);
lean_dec(x_5);
x_84 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_83, x_6);
return x_84;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_24, x_6);
return x_25;
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
lean_inc(x_4);
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Expr_isApp(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_26, x_31);
return x_33;
}
else
{
x_5 = x_26;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_4);
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_39, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_40, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 7:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 2);
lean_inc(x_51);
lean_dec(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_50, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_51, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 3);
lean_inc(x_63);
lean_dec(x_5);
lean_inc(x_4);
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_65);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_4);
x_68 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_62, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_63, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_63);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_64, 0);
lean_dec(x_78);
return x_64;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
lean_dec(x_5);
x_82 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_81, x_6);
return x_82;
}
case 11:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_5, 2);
lean_inc(x_83);
lean_dec(x_5);
x_84 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_83, x_6);
return x_84;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_24, x_6);
return x_25;
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
lean_inc(x_4);
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Expr_isApp(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_26, x_31);
return x_33;
}
else
{
x_5 = x_26;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_4);
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_39, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_40, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 7:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 2);
lean_inc(x_51);
lean_dec(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_50, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_51, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 3);
lean_inc(x_63);
lean_dec(x_5);
lean_inc(x_4);
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_65);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_4);
x_68 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_62, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_63, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_63);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_64, 0);
lean_dec(x_78);
return x_64;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
lean_dec(x_5);
x_82 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_81, x_6);
return x_82;
}
case 11:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_5, 2);
lean_inc(x_83);
lean_dec(x_5);
x_84 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_83, x_6);
return x_84;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_24, x_6);
return x_25;
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
lean_inc(x_4);
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Expr_isApp(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_26, x_31);
return x_33;
}
else
{
x_5 = x_26;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_4);
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_39, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_40, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 7:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 2);
lean_inc(x_51);
lean_dec(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_50, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_51, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 3);
lean_inc(x_63);
lean_dec(x_5);
lean_inc(x_4);
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_65);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_4);
x_68 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_62, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_63, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_63);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_64, 0);
lean_dec(x_78);
return x_64;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
lean_dec(x_5);
x_82 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_81, x_6);
return x_82;
}
case 11:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_5, 2);
lean_inc(x_83);
lean_dec(x_5);
x_84 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_83, x_6);
return x_84;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_5, x_7);
x_11 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = 1;
return x_15;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_5, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_7);
x_18 = 1;
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_7 = x_20;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_4);
x_17 = lean_metavar_ctx_get_expr_assignment(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_MetavarContext_getDecl(x_4, x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_24, x_6);
return x_25;
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
lean_inc(x_4);
x_28 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Expr_isApp(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_26, x_31);
return x_33;
}
else
{
x_5 = x_26;
x_6 = x_31;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_inc(x_40);
lean_dec(x_5);
lean_inc(x_4);
x_41 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_39, x_6);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_40, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 7:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 2);
lean_inc(x_51);
lean_dec(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_50, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_51, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 8:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 3);
lean_inc(x_63);
lean_dec(x_5);
lean_inc(x_4);
x_64 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_61, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_65);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_4);
x_68 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_62, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_63, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_63);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_64, 0);
lean_dec(x_78);
return x_64;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
lean_dec(x_5);
x_82 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_81, x_6);
return x_82;
}
case 11:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_5, 2);
lean_inc(x_83);
lean_dec(x_5);
x_84 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_83, x_6);
return x_84;
}
default: 
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_4);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_19 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(x_1, x_2, x_3, x_4, x_5, x_18);
return x_19;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_fget(x_6, x_8);
lean_inc(x_4);
x_12 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(x_1, x_2, x_3, x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_4);
x_16 = 1;
return x_16;
}
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_85; 
x_85 = lean_nat_dec_lt(x_8, x_7);
if (x_85 == 0)
{
uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_4);
x_86 = 0;
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_array_fget(x_6, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_8, x_88);
lean_dec(x_8);
x_8 = x_89;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_dec(x_87);
x_92 = l_Lean_LocalDecl_fvarId(x_91);
x_93 = lean_ctor_get(x_1, 3);
x_94 = l_Lean_LocalDecl_fvarId(x_93);
x_95 = lean_name_eq(x_92, x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_92, x_2, x_3, x_96);
lean_dec(x_92);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_91, 3);
lean_inc(x_98);
lean_dec(x_91);
x_9 = x_97;
x_10 = x_98;
goto block_39;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_91, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 4);
lean_inc(x_100);
lean_dec(x_91);
x_40 = x_97;
x_41 = x_99;
x_42 = x_100;
goto block_84;
}
}
else
{
lean_dec(x_92);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_91, 3);
lean_inc(x_101);
lean_dec(x_91);
x_102 = 1;
x_9 = x_102;
x_10 = x_101;
goto block_39;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_91, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 4);
lean_inc(x_104);
lean_dec(x_91);
x_105 = 1;
x_40 = x_105;
x_41 = x_103;
x_42 = x_104;
goto block_84;
}
}
}
}
block_39:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasFVar(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasMVar(x_10);
if (x_12 == 0)
{
lean_dec(x_10);
if (x_9 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_4);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_8, x_14);
lean_dec(x_8);
x_8 = x_15;
goto _start;
}
}
else
{
if (x_9 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_10, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_4);
x_21 = 1;
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_8 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_8 = x_26;
goto _start;
}
}
}
else
{
if (x_9 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_29 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_10, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_4);
x_32 = 1;
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_8, x_33);
lean_dec(x_8);
x_8 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_8, x_36);
lean_dec(x_8);
x_8 = x_37;
goto _start;
}
}
}
block_84:
{
lean_object* x_43; uint8_t x_77; 
x_77 = l_Lean_Expr_hasFVar(x_41);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_hasMVar(x_41);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_41);
x_79 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_43 = x_79;
goto block_76;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_41, x_80);
x_43 = x_81;
goto block_76;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_83 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_41, x_82);
x_43 = x_83;
goto block_76;
}
block_76:
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Expr_hasFVar(x_42);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_hasMVar(x_42);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_42);
if (x_40 == 0)
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_4);
x_49 = 1;
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_8, x_50);
lean_dec(x_8);
x_8 = x_51;
goto _start;
}
}
else
{
if (x_40 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_4);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_42, x_46);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
lean_dec(x_8);
lean_dec(x_4);
x_56 = 1;
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_8, x_57);
lean_dec(x_8);
x_8 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
lean_dec(x_42);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_8, x_60);
lean_dec(x_8);
x_8 = x_61;
goto _start;
}
}
}
else
{
if (x_40 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_inc(x_4);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_42, x_46);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_8);
lean_dec(x_4);
x_66 = 1;
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_8, x_67);
lean_dec(x_8);
x_8 = x_68;
goto _start;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_46);
lean_dec(x_42);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_8, x_70);
lean_dec(x_8);
x_8 = x_71;
goto _start;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_43);
lean_dec(x_42);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_8, x_73);
lean_dec(x_8);
x_8 = x_74;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(x_1, x_2, x_3, x_4, x_6, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(x_1, x_2, x_3, x_4, x_10, x_10, x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
uint8_t l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_85; 
x_85 = lean_nat_dec_lt(x_8, x_7);
if (x_85 == 0)
{
uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_4);
x_86 = 0;
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_array_fget(x_6, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_8, x_88);
lean_dec(x_8);
x_8 = x_89;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_dec(x_87);
x_92 = l_Lean_LocalDecl_fvarId(x_91);
x_93 = lean_ctor_get(x_1, 3);
x_94 = l_Lean_LocalDecl_fvarId(x_93);
x_95 = lean_name_eq(x_92, x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_92, x_2, x_3, x_96);
lean_dec(x_92);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_91, 3);
lean_inc(x_98);
lean_dec(x_91);
x_9 = x_97;
x_10 = x_98;
goto block_39;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_91, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 4);
lean_inc(x_100);
lean_dec(x_91);
x_40 = x_97;
x_41 = x_99;
x_42 = x_100;
goto block_84;
}
}
else
{
lean_dec(x_92);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_91, 3);
lean_inc(x_101);
lean_dec(x_91);
x_102 = 1;
x_9 = x_102;
x_10 = x_101;
goto block_39;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_91, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 4);
lean_inc(x_104);
lean_dec(x_91);
x_105 = 1;
x_40 = x_105;
x_41 = x_103;
x_42 = x_104;
goto block_84;
}
}
}
}
block_39:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasFVar(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasMVar(x_10);
if (x_12 == 0)
{
lean_dec(x_10);
if (x_9 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_4);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_8, x_14);
lean_dec(x_8);
x_8 = x_15;
goto _start;
}
}
else
{
if (x_9 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_18 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_10, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_4);
x_21 = 1;
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_8 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_8 = x_26;
goto _start;
}
}
}
else
{
if (x_9 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_29 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_10, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_4);
x_32 = 1;
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_8, x_33);
lean_dec(x_8);
x_8 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_8, x_36);
lean_dec(x_8);
x_8 = x_37;
goto _start;
}
}
}
block_84:
{
lean_object* x_43; uint8_t x_77; 
x_77 = l_Lean_Expr_hasFVar(x_41);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_hasMVar(x_41);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_41);
x_79 = l_Lean_MetavarContext_findLocalDeclDependsOn___closed__1;
x_43 = x_79;
goto block_76;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_81 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_41, x_80);
x_43 = x_81;
goto block_76;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Std_HashSet_Std_Data_HashSet___instance__1___closed__1;
lean_inc(x_4);
x_83 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_41, x_82);
x_43 = x_83;
goto block_76;
}
block_76:
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Expr_hasFVar(x_42);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_hasMVar(x_42);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_42);
if (x_40 == 0)
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_4);
x_49 = 1;
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_8, x_50);
lean_dec(x_8);
x_8 = x_51;
goto _start;
}
}
else
{
if (x_40 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_4);
x_53 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_42, x_46);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
uint8_t x_56; 
lean_dec(x_8);
lean_dec(x_4);
x_56 = 1;
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_8, x_57);
lean_dec(x_8);
x_8 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
lean_dec(x_42);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_8, x_60);
lean_dec(x_8);
x_8 = x_61;
goto _start;
}
}
}
else
{
if (x_40 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_inc(x_4);
x_63 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_42, x_46);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_8);
lean_dec(x_4);
x_66 = 1;
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_8, x_67);
lean_dec(x_8);
x_8 = x_68;
goto _start;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_46);
lean_dec(x_42);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_8, x_70);
lean_dec(x_8);
x_8 = x_71;
goto _start;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_43);
lean_dec(x_42);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_8, x_73);
lean_dec(x_8);
x_8 = x_74;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_4);
x_7 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(x_1, x_2, x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10);
lean_dec(x_9);
return x_11;
}
else
{
lean_dec(x_4);
return x_7;
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_1, x_7, x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_9);
x_12 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_7, x_9, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_st_ref_get(x_3, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_13, 1);
x_19 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_7, x_9, x_17, x_18);
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
x_27 = lean_ctor_get(x_13, 1);
x_28 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_7, x_9, x_26, x_27);
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
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
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
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 1;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__16(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__15(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__14(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__23(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__22(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__20(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__30(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__29(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__28(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__38(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__37(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__40(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__36(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__44(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__47(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__43(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visitMain___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__42(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_0__Lean_MetavarContext_DependsOn_dep_visit___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__50(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__51(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
lean_object* l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__49(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__52(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_hasIndepIndices___spec__48(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
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
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_13);
x_22 = l_Lean_Meta_FVarSubst_get(x_21, x_13);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_8, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_6, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l_Lean_Meta_clear(x_19, x_23, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_31);
lean_dec(x_27);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_4, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_4, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_13, x_21);
lean_dec(x_13);
lean_ctor_set(x_16, 2, x_38);
lean_ctor_set(x_16, 0, x_36);
x_3 = x_15;
x_9 = x_37;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_13, x_21);
lean_dec(x_13);
lean_ctor_set(x_16, 2, x_42);
lean_ctor_set(x_16, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_17);
x_3 = x_15;
x_4 = x_43;
x_9 = x_41;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_16);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_13);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
x_46 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_27, x_5, x_6, x_7, x_8, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_31, x_5, x_6, x_7, x_8, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_3 = x_15;
x_9 = x_49;
goto _start;
}
}
else
{
lean_dec(x_22);
lean_free_object(x_16);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_16, 0);
x_53 = lean_ctor_get(x_16, 1);
x_54 = lean_ctor_get(x_16, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_16);
lean_inc(x_13);
x_55 = l_Lean_Meta_FVarSubst_get(x_54, x_13);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_8, x_9);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_get(x_6, x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_65 = l_Lean_Meta_clear(x_52, x_56, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_64);
lean_dec(x_60);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_66 = x_4;
} else {
 lean_dec_ref(x_4);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_13, x_54);
lean_dec(x_13);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_53);
lean_ctor_set(x_70, 2, x_69);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_17);
x_3 = x_15;
x_4 = x_71;
x_9 = x_68;
goto _start;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_17);
lean_dec(x_13);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec(x_65);
x_74 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_60, x_5, x_6, x_7, x_8, x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_64, x_5, x_6, x_7, x_8, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_3 = x_15;
x_9 = x_77;
goto _start;
}
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_17);
lean_dec(x_13);
x_3 = x_15;
goto _start;
}
}
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = x_4;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_4, x_3, x_15);
x_17 = x_14;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(x_1, x_2, x_15, x_17, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = x_19;
x_24 = lean_array_fset(x_16, x_3, x_23);
lean_dec(x_3);
x_3 = x_22;
x_4 = x_24;
x_9 = x_20;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = x_2;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_9);
x_12 = x_11;
x_13 = lean_apply_5(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = x_6;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_array_fget(x_6, x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_6, x_5, x_11);
x_13 = x_10;
x_14 = l_Lean_Init_LeanInit___instance__1;
x_15 = lean_array_get(x_14, x_1, x_5);
lean_inc(x_3);
lean_inc(x_15);
x_16 = l_Lean_mkConst(x_15, x_3);
x_17 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_4, x_4, x_11, x_16);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_13, 2);
x_21 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_19, x_19, x_11, x_17);
lean_inc(x_2);
x_22 = l_Lean_Meta_FVarSubst_insert(x_20, x_2, x_21);
lean_ctor_set(x_13, 2, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
x_26 = x_23;
x_27 = lean_array_fset(x_12, x_5, x_26);
lean_dec(x_5);
x_5 = x_25;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
x_31 = lean_ctor_get(x_13, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_32 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_30, x_30, x_11, x_17);
lean_inc(x_2);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_2, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_15);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_5, x_36);
x_38 = x_35;
x_39 = lean_array_fset(x_12, x_5, x_38);
lean_dec(x_5);
x_5 = x_37;
x_6 = x_39;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = x_1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(x_2, x_3, x_4, x_5, x_7, x_6);
x_9 = x_8;
return x_9;
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
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
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_LocalDecl_type(x_13);
x_16 = l_Lean_Expr_heq_x3f___closed__2;
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Expr_isAppOfArity(x_15, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_eq_x3f___closed__2;
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Expr_isAppOfArity(x_15, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_22 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2;
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkNoConfusionImp___closed__5;
x_24 = lean_box(0);
x_25 = l_Lean_Meta_throwTacticEx___rarg(x_22, x_2, x_23, x_24, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Expr_appFn_x21(x_15);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_28);
lean_inc(x_27);
x_29 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_27, x_28, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_27);
x_33 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_27, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_28);
x_36 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_28, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_expr_eqv(x_34, x_27);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
lean_dec(x_27);
lean_inc(x_1);
x_40 = l_Lean_mkFVar(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_41 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_34, x_37, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_LocalDecl_userName(x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = l_Lean_Meta_assert(x_2, x_44, x_42, x_40, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_48 = l_Lean_Meta_clear(x_46, x_1, x_7, x_8, x_9, x_10, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_3, x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_4);
lean_ctor_set(x_53, 2, x_5);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_6);
x_55 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_52, x_54, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_52);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_45);
if (x_60 == 0)
{
return x_45;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_45, 0);
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_45);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_41);
if (x_64 == 0)
{
return x_41;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_41, 0);
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_41);
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
x_68 = lean_expr_eqv(x_37, x_28);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_28);
lean_dec(x_27);
lean_inc(x_1);
x_69 = l_Lean_mkFVar(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_70 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_34, x_37, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_LocalDecl_userName(x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_74 = l_Lean_Meta_assert(x_2, x_73, x_71, x_69, x_7, x_8, x_9, x_10, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_77 = l_Lean_Meta_clear(x_75, x_1, x_7, x_8, x_9, x_10, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_3, x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_4);
lean_ctor_set(x_82, 2, x_5);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_6);
x_84 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_81, x_83, x_7, x_8, x_9, x_10, x_79);
lean_dec(x_81);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_74);
if (x_89 == 0)
{
return x_74;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_74, 0);
x_91 = lean_ctor_get(x_74, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_74);
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
lean_dec(x_69);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_70);
if (x_93 == 0)
{
return x_70;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_70, 0);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_70);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_13);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_97; lean_object* x_98; 
lean_dec(x_28);
x_97 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_98 = l_Lean_Meta_substCore(x_2, x_1, x_97, x_5, x_97, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = x_4;
x_104 = lean_unsigned_to_nat(0u);
lean_inc(x_101);
x_105 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__1(x_101, x_104, x_103);
x_106 = x_105;
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_101);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_6);
x_109 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_108, x_7, x_8, x_9, x_10, x_100);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_98);
if (x_110 == 0)
{
return x_98;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_98, 0);
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_98);
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
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_128 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_125, x_127, x_7, x_8, x_9, x_10, x_122);
lean_dec(x_125);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
switch (lean_obj_tag(x_28)) {
case 0:
{
uint8_t x_133; uint8_t x_134; lean_object* x_135; 
lean_dec(x_28);
lean_dec(x_27);
x_133 = 0;
x_134 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_135 = l_Lean_Meta_substCore(x_2, x_1, x_133, x_5, x_134, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
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
x_140 = x_4;
x_141 = lean_unsigned_to_nat(0u);
lean_inc(x_138);
x_142 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__2(x_138, x_141, x_140);
x_143 = x_142;
x_144 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_144, 0, x_139);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_138);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_6);
x_146 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_145, x_7, x_8, x_9, x_10, x_137);
return x_146;
}
else
{
uint8_t x_147; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_147 = !lean_is_exclusive(x_135);
if (x_147 == 0)
{
return x_135;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_135, 0);
x_149 = lean_ctor_get(x_135, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_135);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
case 1:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_27, 0);
lean_inc(x_151);
lean_dec(x_27);
x_152 = lean_ctor_get(x_28, 0);
lean_inc(x_152);
lean_dec(x_28);
lean_inc(x_7);
x_153 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_151, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_7);
x_156 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_152, x_7, x_8, x_9, x_10, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_LocalDecl_index(x_154);
lean_dec(x_154);
x_160 = l_Lean_LocalDecl_index(x_157);
lean_dec(x_157);
x_161 = lean_nat_dec_lt(x_159, x_160);
lean_dec(x_160);
lean_dec(x_159);
x_162 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_163 = l_Lean_Meta_substCore(x_2, x_1, x_161, x_5, x_162, x_7, x_8, x_9, x_10, x_158);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = x_4;
x_169 = lean_unsigned_to_nat(0u);
lean_inc(x_166);
x_170 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__3(x_166, x_169, x_168);
x_171 = x_170;
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_166);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_6);
x_174 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_173, x_7, x_8, x_9, x_10, x_165);
return x_174;
}
else
{
uint8_t x_175; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_175 = !lean_is_exclusive(x_163);
if (x_175 == 0)
{
return x_163;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_163, 0);
x_177 = lean_ctor_get(x_163, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_163);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_154);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_156);
if (x_179 == 0)
{
return x_156;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_156, 0);
x_181 = lean_ctor_get(x_156, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_156);
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
lean_dec(x_152);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_153);
if (x_183 == 0)
{
return x_153;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_153, 0);
x_185 = lean_ctor_get(x_153, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_153);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
case 2:
{
uint8_t x_187; uint8_t x_188; lean_object* x_189; 
lean_dec(x_28);
lean_dec(x_27);
x_187 = 0;
x_188 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_189 = l_Lean_Meta_substCore(x_2, x_1, x_187, x_5, x_188, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_194 = x_4;
x_195 = lean_unsigned_to_nat(0u);
lean_inc(x_192);
x_196 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__4(x_192, x_195, x_194);
x_197 = x_196;
x_198 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_192);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_6);
x_200 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_199, x_7, x_8, x_9, x_10, x_191);
return x_200;
}
else
{
uint8_t x_201; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_201 = !lean_is_exclusive(x_189);
if (x_201 == 0)
{
return x_189;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_189, 0);
x_203 = lean_ctor_get(x_189, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_189);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
case 3:
{
uint8_t x_205; uint8_t x_206; lean_object* x_207; 
lean_dec(x_28);
lean_dec(x_27);
x_205 = 0;
x_206 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_207 = l_Lean_Meta_substCore(x_2, x_1, x_205, x_5, x_206, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = x_4;
x_213 = lean_unsigned_to_nat(0u);
lean_inc(x_210);
x_214 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__5(x_210, x_213, x_212);
x_215 = x_214;
x_216 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_216, 2, x_210);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_6);
x_218 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_217, x_7, x_8, x_9, x_10, x_209);
return x_218;
}
else
{
uint8_t x_219; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_219 = !lean_is_exclusive(x_207);
if (x_219 == 0)
{
return x_207;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_207, 0);
x_221 = lean_ctor_get(x_207, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_207);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
case 4:
{
uint8_t x_223; uint8_t x_224; lean_object* x_225; 
lean_dec(x_28);
lean_dec(x_27);
x_223 = 0;
x_224 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_225 = l_Lean_Meta_substCore(x_2, x_1, x_223, x_5, x_224, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
x_230 = x_4;
x_231 = lean_unsigned_to_nat(0u);
lean_inc(x_228);
x_232 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__6(x_228, x_231, x_230);
x_233 = x_232;
x_234 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_234, 0, x_229);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_228);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_6);
x_236 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_235, x_7, x_8, x_9, x_10, x_227);
return x_236;
}
else
{
uint8_t x_237; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_237 = !lean_is_exclusive(x_225);
if (x_237 == 0)
{
return x_225;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_225, 0);
x_239 = lean_ctor_get(x_225, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_225);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
case 5:
{
uint8_t x_241; uint8_t x_242; lean_object* x_243; 
lean_dec(x_28);
lean_dec(x_27);
x_241 = 0;
x_242 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_243 = l_Lean_Meta_substCore(x_2, x_1, x_241, x_5, x_242, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_248 = x_4;
x_249 = lean_unsigned_to_nat(0u);
lean_inc(x_246);
x_250 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__7(x_246, x_249, x_248);
x_251 = x_250;
x_252 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_252, 0, x_247);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_252, 2, x_246);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_6);
x_254 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_253, x_7, x_8, x_9, x_10, x_245);
return x_254;
}
else
{
uint8_t x_255; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_255 = !lean_is_exclusive(x_243);
if (x_255 == 0)
{
return x_243;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_243, 0);
x_257 = lean_ctor_get(x_243, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_243);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
case 6:
{
uint8_t x_259; uint8_t x_260; lean_object* x_261; 
lean_dec(x_28);
lean_dec(x_27);
x_259 = 0;
x_260 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_261 = l_Lean_Meta_substCore(x_2, x_1, x_259, x_5, x_260, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = x_4;
x_267 = lean_unsigned_to_nat(0u);
lean_inc(x_264);
x_268 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__8(x_264, x_267, x_266);
x_269 = x_268;
x_270 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_270, 0, x_265);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_270, 2, x_264);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_6);
x_272 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_271, x_7, x_8, x_9, x_10, x_263);
return x_272;
}
else
{
uint8_t x_273; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_273 = !lean_is_exclusive(x_261);
if (x_273 == 0)
{
return x_261;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_261, 0);
x_275 = lean_ctor_get(x_261, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_261);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
case 7:
{
uint8_t x_277; uint8_t x_278; lean_object* x_279; 
lean_dec(x_28);
lean_dec(x_27);
x_277 = 0;
x_278 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_279 = l_Lean_Meta_substCore(x_2, x_1, x_277, x_5, x_278, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = x_4;
x_285 = lean_unsigned_to_nat(0u);
lean_inc(x_282);
x_286 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__9(x_282, x_285, x_284);
x_287 = x_286;
x_288 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_288, 0, x_283);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_282);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_6);
x_290 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_289, x_7, x_8, x_9, x_10, x_281);
return x_290;
}
else
{
uint8_t x_291; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_291 = !lean_is_exclusive(x_279);
if (x_291 == 0)
{
return x_279;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_279, 0);
x_293 = lean_ctor_get(x_279, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_279);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
case 8:
{
uint8_t x_295; uint8_t x_296; lean_object* x_297; 
lean_dec(x_28);
lean_dec(x_27);
x_295 = 0;
x_296 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_297 = l_Lean_Meta_substCore(x_2, x_1, x_295, x_5, x_296, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = x_4;
x_303 = lean_unsigned_to_nat(0u);
lean_inc(x_300);
x_304 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__10(x_300, x_303, x_302);
x_305 = x_304;
x_306 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_306, 0, x_301);
lean_ctor_set(x_306, 1, x_305);
lean_ctor_set(x_306, 2, x_300);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_6);
x_308 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_307, x_7, x_8, x_9, x_10, x_299);
return x_308;
}
else
{
uint8_t x_309; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_309 = !lean_is_exclusive(x_297);
if (x_309 == 0)
{
return x_297;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_297, 0);
x_311 = lean_ctor_get(x_297, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_297);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
case 9:
{
uint8_t x_313; uint8_t x_314; lean_object* x_315; 
lean_dec(x_28);
lean_dec(x_27);
x_313 = 0;
x_314 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_315 = l_Lean_Meta_substCore(x_2, x_1, x_313, x_5, x_314, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_dec(x_316);
x_320 = x_4;
x_321 = lean_unsigned_to_nat(0u);
lean_inc(x_318);
x_322 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__11(x_318, x_321, x_320);
x_323 = x_322;
x_324 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_324, 0, x_319);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set(x_324, 2, x_318);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_6);
x_326 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_325, x_7, x_8, x_9, x_10, x_317);
return x_326;
}
else
{
uint8_t x_327; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_327 = !lean_is_exclusive(x_315);
if (x_327 == 0)
{
return x_315;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_315, 0);
x_329 = lean_ctor_get(x_315, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_315);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
case 10:
{
uint8_t x_331; uint8_t x_332; lean_object* x_333; 
lean_dec(x_28);
lean_dec(x_27);
x_331 = 0;
x_332 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_333 = l_Lean_Meta_substCore(x_2, x_1, x_331, x_5, x_332, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
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
x_338 = x_4;
x_339 = lean_unsigned_to_nat(0u);
lean_inc(x_336);
x_340 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__12(x_336, x_339, x_338);
x_341 = x_340;
x_342 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_342, 0, x_337);
lean_ctor_set(x_342, 1, x_341);
lean_ctor_set(x_342, 2, x_336);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_6);
x_344 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_343, x_7, x_8, x_9, x_10, x_335);
return x_344;
}
else
{
uint8_t x_345; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_345 = !lean_is_exclusive(x_333);
if (x_345 == 0)
{
return x_333;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_333, 0);
x_347 = lean_ctor_get(x_333, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_333);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
case 11:
{
uint8_t x_349; uint8_t x_350; lean_object* x_351; 
lean_dec(x_28);
lean_dec(x_27);
x_349 = 0;
x_350 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_351 = l_Lean_Meta_substCore(x_2, x_1, x_349, x_5, x_350, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
lean_dec(x_352);
x_356 = x_4;
x_357 = lean_unsigned_to_nat(0u);
lean_inc(x_354);
x_358 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__13(x_354, x_357, x_356);
x_359 = x_358;
x_360 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set(x_360, 2, x_354);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_6);
x_362 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_361, x_7, x_8, x_9, x_10, x_353);
return x_362;
}
else
{
uint8_t x_363; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_363 = !lean_is_exclusive(x_351);
if (x_363 == 0)
{
return x_351;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_351, 0);
x_365 = lean_ctor_get(x_351, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_351);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
default: 
{
uint8_t x_367; uint8_t x_368; lean_object* x_369; 
lean_dec(x_28);
lean_dec(x_27);
x_367 = 0;
x_368 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_369 = l_Lean_Meta_substCore(x_2, x_1, x_367, x_5, x_368, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
lean_dec(x_370);
x_374 = x_4;
x_375 = lean_unsigned_to_nat(0u);
lean_inc(x_372);
x_376 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__14(x_372, x_375, x_374);
x_377 = x_376;
x_378 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_377);
lean_ctor_set(x_378, 2, x_372);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_6);
x_380 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_379, x_7, x_8, x_9, x_10, x_371);
return x_380;
}
else
{
uint8_t x_381; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_381 = !lean_is_exclusive(x_369);
if (x_381 == 0)
{
return x_369;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_369, 0);
x_383 = lean_ctor_get(x_369, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_369);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
}
case 2:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_385; lean_object* x_386; 
lean_dec(x_28);
x_385 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_386 = l_Lean_Meta_substCore(x_2, x_1, x_385, x_5, x_385, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_ctor_get(x_387, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
lean_dec(x_387);
x_391 = x_4;
x_392 = lean_unsigned_to_nat(0u);
lean_inc(x_389);
x_393 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__15(x_389, x_392, x_391);
x_394 = x_393;
x_395 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_395, 0, x_390);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set(x_395, 2, x_389);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_6);
x_397 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_396, x_7, x_8, x_9, x_10, x_388);
return x_397;
}
else
{
uint8_t x_398; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_398 = !lean_is_exclusive(x_386);
if (x_398 == 0)
{
return x_386;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_386, 0);
x_400 = lean_ctor_get(x_386, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_386);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
}
}
else
{
lean_object* x_402; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_402 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
if (lean_obj_tag(x_403) == 0)
{
uint8_t x_404; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_404 = !lean_is_exclusive(x_402);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_402, 0);
lean_dec(x_405);
x_406 = lean_box(0);
lean_ctor_set(x_402, 0, x_406);
return x_402;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_402, 1);
lean_inc(x_407);
lean_dec(x_402);
x_408 = lean_box(0);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_410 = lean_ctor_get(x_402, 1);
lean_inc(x_410);
lean_dec(x_402);
x_411 = lean_ctor_get(x_403, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_403, 1);
lean_inc(x_412);
lean_dec(x_403);
x_413 = lean_nat_add(x_3, x_412);
lean_dec(x_412);
x_414 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_4);
lean_ctor_set(x_414, 2, x_5);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_6);
x_416 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_413, x_415, x_7, x_8, x_9, x_10, x_410);
lean_dec(x_413);
return x_416;
}
}
else
{
uint8_t x_417; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_417 = !lean_is_exclusive(x_402);
if (x_417 == 0)
{
return x_402;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_402, 0);
x_419 = lean_ctor_get(x_402, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_402);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
case 3:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_421; lean_object* x_422; 
lean_dec(x_28);
x_421 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_422 = l_Lean_Meta_substCore(x_2, x_1, x_421, x_5, x_421, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_dec(x_423);
x_427 = x_4;
x_428 = lean_unsigned_to_nat(0u);
lean_inc(x_425);
x_429 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__16(x_425, x_428, x_427);
x_430 = x_429;
x_431 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_431, 0, x_426);
lean_ctor_set(x_431, 1, x_430);
lean_ctor_set(x_431, 2, x_425);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_6);
x_433 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_432, x_7, x_8, x_9, x_10, x_424);
return x_433;
}
else
{
uint8_t x_434; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_434 = !lean_is_exclusive(x_422);
if (x_434 == 0)
{
return x_422;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_422, 0);
x_436 = lean_ctor_get(x_422, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_422);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
else
{
lean_object* x_438; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_438 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
if (lean_obj_tag(x_439) == 0)
{
uint8_t x_440; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_440 = !lean_is_exclusive(x_438);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_438, 0);
lean_dec(x_441);
x_442 = lean_box(0);
lean_ctor_set(x_438, 0, x_442);
return x_438;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_438, 1);
lean_inc(x_443);
lean_dec(x_438);
x_444 = lean_box(0);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_446 = lean_ctor_get(x_438, 1);
lean_inc(x_446);
lean_dec(x_438);
x_447 = lean_ctor_get(x_439, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_439, 1);
lean_inc(x_448);
lean_dec(x_439);
x_449 = lean_nat_add(x_3, x_448);
lean_dec(x_448);
x_450 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_4);
lean_ctor_set(x_450, 2, x_5);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_6);
x_452 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_449, x_451, x_7, x_8, x_9, x_10, x_446);
lean_dec(x_449);
return x_452;
}
}
else
{
uint8_t x_453; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_453 = !lean_is_exclusive(x_438);
if (x_453 == 0)
{
return x_438;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_438, 0);
x_455 = lean_ctor_get(x_438, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_438);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
}
case 4:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_457; lean_object* x_458; 
lean_dec(x_28);
x_457 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_458 = l_Lean_Meta_substCore(x_2, x_1, x_457, x_5, x_457, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
lean_dec(x_459);
x_463 = x_4;
x_464 = lean_unsigned_to_nat(0u);
lean_inc(x_461);
x_465 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__17(x_461, x_464, x_463);
x_466 = x_465;
x_467 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_467, 0, x_462);
lean_ctor_set(x_467, 1, x_466);
lean_ctor_set(x_467, 2, x_461);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_6);
x_469 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_468, x_7, x_8, x_9, x_10, x_460);
return x_469;
}
else
{
uint8_t x_470; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_470 = !lean_is_exclusive(x_458);
if (x_470 == 0)
{
return x_458;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_458, 0);
x_472 = lean_ctor_get(x_458, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_458);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
else
{
lean_object* x_474; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_474 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
uint8_t x_476; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_476 = !lean_is_exclusive(x_474);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_474, 0);
lean_dec(x_477);
x_478 = lean_box(0);
lean_ctor_set(x_474, 0, x_478);
return x_474;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_474, 1);
lean_inc(x_479);
lean_dec(x_474);
x_480 = lean_box(0);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_479);
return x_481;
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_482 = lean_ctor_get(x_474, 1);
lean_inc(x_482);
lean_dec(x_474);
x_483 = lean_ctor_get(x_475, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_475, 1);
lean_inc(x_484);
lean_dec(x_475);
x_485 = lean_nat_add(x_3, x_484);
lean_dec(x_484);
x_486 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_4);
lean_ctor_set(x_486, 2, x_5);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_6);
x_488 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_485, x_487, x_7, x_8, x_9, x_10, x_482);
lean_dec(x_485);
return x_488;
}
}
else
{
uint8_t x_489; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_489 = !lean_is_exclusive(x_474);
if (x_489 == 0)
{
return x_474;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_474, 0);
x_491 = lean_ctor_get(x_474, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_474);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
}
case 5:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_493; lean_object* x_494; 
lean_dec(x_28);
x_493 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_494 = l_Lean_Meta_substCore(x_2, x_1, x_493, x_5, x_493, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_dec(x_495);
x_499 = x_4;
x_500 = lean_unsigned_to_nat(0u);
lean_inc(x_497);
x_501 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__18(x_497, x_500, x_499);
x_502 = x_501;
x_503 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_503, 0, x_498);
lean_ctor_set(x_503, 1, x_502);
lean_ctor_set(x_503, 2, x_497);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_6);
x_505 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_504, x_7, x_8, x_9, x_10, x_496);
return x_505;
}
else
{
uint8_t x_506; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_506 = !lean_is_exclusive(x_494);
if (x_506 == 0)
{
return x_494;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_494, 0);
x_508 = lean_ctor_get(x_494, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_494);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
else
{
lean_object* x_510; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_510 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
if (lean_obj_tag(x_511) == 0)
{
uint8_t x_512; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_512 = !lean_is_exclusive(x_510);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; 
x_513 = lean_ctor_get(x_510, 0);
lean_dec(x_513);
x_514 = lean_box(0);
lean_ctor_set(x_510, 0, x_514);
return x_510;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_510, 1);
lean_inc(x_515);
lean_dec(x_510);
x_516 = lean_box(0);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_515);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_518 = lean_ctor_get(x_510, 1);
lean_inc(x_518);
lean_dec(x_510);
x_519 = lean_ctor_get(x_511, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_511, 1);
lean_inc(x_520);
lean_dec(x_511);
x_521 = lean_nat_add(x_3, x_520);
lean_dec(x_520);
x_522 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_4);
lean_ctor_set(x_522, 2, x_5);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_6);
x_524 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_521, x_523, x_7, x_8, x_9, x_10, x_518);
lean_dec(x_521);
return x_524;
}
}
else
{
uint8_t x_525; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_525 = !lean_is_exclusive(x_510);
if (x_525 == 0)
{
return x_510;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_510, 0);
x_527 = lean_ctor_get(x_510, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_510);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
return x_528;
}
}
}
}
case 6:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_529; lean_object* x_530; 
lean_dec(x_28);
x_529 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_530 = l_Lean_Meta_substCore(x_2, x_1, x_529, x_5, x_529, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = lean_ctor_get(x_531, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_531, 1);
lean_inc(x_534);
lean_dec(x_531);
x_535 = x_4;
x_536 = lean_unsigned_to_nat(0u);
lean_inc(x_533);
x_537 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__19(x_533, x_536, x_535);
x_538 = x_537;
x_539 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_539, 0, x_534);
lean_ctor_set(x_539, 1, x_538);
lean_ctor_set(x_539, 2, x_533);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_6);
x_541 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_540, x_7, x_8, x_9, x_10, x_532);
return x_541;
}
else
{
uint8_t x_542; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_542 = !lean_is_exclusive(x_530);
if (x_542 == 0)
{
return x_530;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_530, 0);
x_544 = lean_ctor_get(x_530, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_530);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
return x_545;
}
}
}
else
{
lean_object* x_546; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_546 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
if (lean_obj_tag(x_547) == 0)
{
uint8_t x_548; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_548 = !lean_is_exclusive(x_546);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_ctor_get(x_546, 0);
lean_dec(x_549);
x_550 = lean_box(0);
lean_ctor_set(x_546, 0, x_550);
return x_546;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_546, 1);
lean_inc(x_551);
lean_dec(x_546);
x_552 = lean_box(0);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_551);
return x_553;
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_554 = lean_ctor_get(x_546, 1);
lean_inc(x_554);
lean_dec(x_546);
x_555 = lean_ctor_get(x_547, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_547, 1);
lean_inc(x_556);
lean_dec(x_547);
x_557 = lean_nat_add(x_3, x_556);
lean_dec(x_556);
x_558 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_4);
lean_ctor_set(x_558, 2, x_5);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_6);
x_560 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_557, x_559, x_7, x_8, x_9, x_10, x_554);
lean_dec(x_557);
return x_560;
}
}
else
{
uint8_t x_561; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_561 = !lean_is_exclusive(x_546);
if (x_561 == 0)
{
return x_546;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_546, 0);
x_563 = lean_ctor_get(x_546, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_546);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
}
case 7:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_565; lean_object* x_566; 
lean_dec(x_28);
x_565 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_566 = l_Lean_Meta_substCore(x_2, x_1, x_565, x_5, x_565, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_ctor_get(x_567, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_567, 1);
lean_inc(x_570);
lean_dec(x_567);
x_571 = x_4;
x_572 = lean_unsigned_to_nat(0u);
lean_inc(x_569);
x_573 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__20(x_569, x_572, x_571);
x_574 = x_573;
x_575 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_575, 0, x_570);
lean_ctor_set(x_575, 1, x_574);
lean_ctor_set(x_575, 2, x_569);
x_576 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_6);
x_577 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_576, x_7, x_8, x_9, x_10, x_568);
return x_577;
}
else
{
uint8_t x_578; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_578 = !lean_is_exclusive(x_566);
if (x_578 == 0)
{
return x_566;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_566, 0);
x_580 = lean_ctor_get(x_566, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_566);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
return x_581;
}
}
}
else
{
lean_object* x_582; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_582 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
if (lean_obj_tag(x_583) == 0)
{
uint8_t x_584; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_584 = !lean_is_exclusive(x_582);
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_582, 0);
lean_dec(x_585);
x_586 = lean_box(0);
lean_ctor_set(x_582, 0, x_586);
return x_582;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_582, 1);
lean_inc(x_587);
lean_dec(x_582);
x_588 = lean_box(0);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_587);
return x_589;
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_590 = lean_ctor_get(x_582, 1);
lean_inc(x_590);
lean_dec(x_582);
x_591 = lean_ctor_get(x_583, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_583, 1);
lean_inc(x_592);
lean_dec(x_583);
x_593 = lean_nat_add(x_3, x_592);
lean_dec(x_592);
x_594 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_4);
lean_ctor_set(x_594, 2, x_5);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_6);
x_596 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_593, x_595, x_7, x_8, x_9, x_10, x_590);
lean_dec(x_593);
return x_596;
}
}
else
{
uint8_t x_597; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_597 = !lean_is_exclusive(x_582);
if (x_597 == 0)
{
return x_582;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_582, 0);
x_599 = lean_ctor_get(x_582, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_582);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
return x_600;
}
}
}
}
case 8:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_601; lean_object* x_602; 
lean_dec(x_28);
x_601 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_602 = l_Lean_Meta_substCore(x_2, x_1, x_601, x_5, x_601, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = lean_ctor_get(x_603, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_603, 1);
lean_inc(x_606);
lean_dec(x_603);
x_607 = x_4;
x_608 = lean_unsigned_to_nat(0u);
lean_inc(x_605);
x_609 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__21(x_605, x_608, x_607);
x_610 = x_609;
x_611 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_611, 0, x_606);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set(x_611, 2, x_605);
x_612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_6);
x_613 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_612, x_7, x_8, x_9, x_10, x_604);
return x_613;
}
else
{
uint8_t x_614; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_614 = !lean_is_exclusive(x_602);
if (x_614 == 0)
{
return x_602;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_602, 0);
x_616 = lean_ctor_get(x_602, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_602);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
return x_617;
}
}
}
else
{
lean_object* x_618; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_618 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
if (lean_obj_tag(x_619) == 0)
{
uint8_t x_620; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_620 = !lean_is_exclusive(x_618);
if (x_620 == 0)
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_618, 0);
lean_dec(x_621);
x_622 = lean_box(0);
lean_ctor_set(x_618, 0, x_622);
return x_618;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_618, 1);
lean_inc(x_623);
lean_dec(x_618);
x_624 = lean_box(0);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_623);
return x_625;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_626 = lean_ctor_get(x_618, 1);
lean_inc(x_626);
lean_dec(x_618);
x_627 = lean_ctor_get(x_619, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_619, 1);
lean_inc(x_628);
lean_dec(x_619);
x_629 = lean_nat_add(x_3, x_628);
lean_dec(x_628);
x_630 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_4);
lean_ctor_set(x_630, 2, x_5);
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_6);
x_632 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_629, x_631, x_7, x_8, x_9, x_10, x_626);
lean_dec(x_629);
return x_632;
}
}
else
{
uint8_t x_633; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_633 = !lean_is_exclusive(x_618);
if (x_633 == 0)
{
return x_618;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_618, 0);
x_635 = lean_ctor_get(x_618, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_618);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
}
}
case 9:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_637; lean_object* x_638; 
lean_dec(x_28);
x_637 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_638 = l_Lean_Meta_substCore(x_2, x_1, x_637, x_5, x_637, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = lean_ctor_get(x_639, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_639, 1);
lean_inc(x_642);
lean_dec(x_639);
x_643 = x_4;
x_644 = lean_unsigned_to_nat(0u);
lean_inc(x_641);
x_645 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__22(x_641, x_644, x_643);
x_646 = x_645;
x_647 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_647, 0, x_642);
lean_ctor_set(x_647, 1, x_646);
lean_ctor_set(x_647, 2, x_641);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_6);
x_649 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_648, x_7, x_8, x_9, x_10, x_640);
return x_649;
}
else
{
uint8_t x_650; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_650 = !lean_is_exclusive(x_638);
if (x_650 == 0)
{
return x_638;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_638, 0);
x_652 = lean_ctor_get(x_638, 1);
lean_inc(x_652);
lean_inc(x_651);
lean_dec(x_638);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
return x_653;
}
}
}
else
{
lean_object* x_654; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_654 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
if (lean_obj_tag(x_655) == 0)
{
uint8_t x_656; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_656 = !lean_is_exclusive(x_654);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; 
x_657 = lean_ctor_get(x_654, 0);
lean_dec(x_657);
x_658 = lean_box(0);
lean_ctor_set(x_654, 0, x_658);
return x_654;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_654, 1);
lean_inc(x_659);
lean_dec(x_654);
x_660 = lean_box(0);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_662 = lean_ctor_get(x_654, 1);
lean_inc(x_662);
lean_dec(x_654);
x_663 = lean_ctor_get(x_655, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_655, 1);
lean_inc(x_664);
lean_dec(x_655);
x_665 = lean_nat_add(x_3, x_664);
lean_dec(x_664);
x_666 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_666, 0, x_663);
lean_ctor_set(x_666, 1, x_4);
lean_ctor_set(x_666, 2, x_5);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_6);
x_668 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_665, x_667, x_7, x_8, x_9, x_10, x_662);
lean_dec(x_665);
return x_668;
}
}
else
{
uint8_t x_669; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_669 = !lean_is_exclusive(x_654);
if (x_669 == 0)
{
return x_654;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_654, 0);
x_671 = lean_ctor_get(x_654, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_654);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
}
}
case 10:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_673; lean_object* x_674; 
lean_dec(x_28);
x_673 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_674 = l_Lean_Meta_substCore(x_2, x_1, x_673, x_5, x_673, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_677 = lean_ctor_get(x_675, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_675, 1);
lean_inc(x_678);
lean_dec(x_675);
x_679 = x_4;
x_680 = lean_unsigned_to_nat(0u);
lean_inc(x_677);
x_681 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__23(x_677, x_680, x_679);
x_682 = x_681;
x_683 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_683, 0, x_678);
lean_ctor_set(x_683, 1, x_682);
lean_ctor_set(x_683, 2, x_677);
x_684 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_6);
x_685 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_684, x_7, x_8, x_9, x_10, x_676);
return x_685;
}
else
{
uint8_t x_686; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_686 = !lean_is_exclusive(x_674);
if (x_686 == 0)
{
return x_674;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_674, 0);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
lean_inc(x_687);
lean_dec(x_674);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
return x_689;
}
}
}
else
{
lean_object* x_690; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_690 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
if (lean_obj_tag(x_691) == 0)
{
uint8_t x_692; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_692 = !lean_is_exclusive(x_690);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; 
x_693 = lean_ctor_get(x_690, 0);
lean_dec(x_693);
x_694 = lean_box(0);
lean_ctor_set(x_690, 0, x_694);
return x_690;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_690, 1);
lean_inc(x_695);
lean_dec(x_690);
x_696 = lean_box(0);
x_697 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_695);
return x_697;
}
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_698 = lean_ctor_get(x_690, 1);
lean_inc(x_698);
lean_dec(x_690);
x_699 = lean_ctor_get(x_691, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_691, 1);
lean_inc(x_700);
lean_dec(x_691);
x_701 = lean_nat_add(x_3, x_700);
lean_dec(x_700);
x_702 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_4);
lean_ctor_set(x_702, 2, x_5);
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_6);
x_704 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_701, x_703, x_7, x_8, x_9, x_10, x_698);
lean_dec(x_701);
return x_704;
}
}
else
{
uint8_t x_705; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_705 = !lean_is_exclusive(x_690);
if (x_705 == 0)
{
return x_690;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_690, 0);
x_707 = lean_ctor_get(x_690, 1);
lean_inc(x_707);
lean_inc(x_706);
lean_dec(x_690);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_706);
lean_ctor_set(x_708, 1, x_707);
return x_708;
}
}
}
}
case 11:
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_709; lean_object* x_710; 
lean_dec(x_28);
x_709 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_710 = l_Lean_Meta_substCore(x_2, x_1, x_709, x_5, x_709, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_710, 1);
lean_inc(x_712);
lean_dec(x_710);
x_713 = lean_ctor_get(x_711, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_711, 1);
lean_inc(x_714);
lean_dec(x_711);
x_715 = x_4;
x_716 = lean_unsigned_to_nat(0u);
lean_inc(x_713);
x_717 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__24(x_713, x_716, x_715);
x_718 = x_717;
x_719 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_719, 0, x_714);
lean_ctor_set(x_719, 1, x_718);
lean_ctor_set(x_719, 2, x_713);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_6);
x_721 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_720, x_7, x_8, x_9, x_10, x_712);
return x_721;
}
else
{
uint8_t x_722; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_722 = !lean_is_exclusive(x_710);
if (x_722 == 0)
{
return x_710;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_710, 0);
x_724 = lean_ctor_get(x_710, 1);
lean_inc(x_724);
lean_inc(x_723);
lean_dec(x_710);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_723);
lean_ctor_set(x_725, 1, x_724);
return x_725;
}
}
}
else
{
lean_object* x_726; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_726 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; 
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
if (lean_obj_tag(x_727) == 0)
{
uint8_t x_728; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_728 = !lean_is_exclusive(x_726);
if (x_728 == 0)
{
lean_object* x_729; lean_object* x_730; 
x_729 = lean_ctor_get(x_726, 0);
lean_dec(x_729);
x_730 = lean_box(0);
lean_ctor_set(x_726, 0, x_730);
return x_726;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_731 = lean_ctor_get(x_726, 1);
lean_inc(x_731);
lean_dec(x_726);
x_732 = lean_box(0);
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_731);
return x_733;
}
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_734 = lean_ctor_get(x_726, 1);
lean_inc(x_734);
lean_dec(x_726);
x_735 = lean_ctor_get(x_727, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_727, 1);
lean_inc(x_736);
lean_dec(x_727);
x_737 = lean_nat_add(x_3, x_736);
lean_dec(x_736);
x_738 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_738, 0, x_735);
lean_ctor_set(x_738, 1, x_4);
lean_ctor_set(x_738, 2, x_5);
x_739 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_6);
x_740 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_737, x_739, x_7, x_8, x_9, x_10, x_734);
lean_dec(x_737);
return x_740;
}
}
else
{
uint8_t x_741; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_741 = !lean_is_exclusive(x_726);
if (x_741 == 0)
{
return x_726;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_726, 0);
x_743 = lean_ctor_get(x_726, 1);
lean_inc(x_743);
lean_inc(x_742);
lean_dec(x_726);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
}
}
}
default: 
{
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
uint8_t x_745; lean_object* x_746; 
lean_dec(x_28);
x_745 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_746 = l_Lean_Meta_substCore(x_2, x_1, x_745, x_5, x_745, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec(x_746);
x_749 = lean_ctor_get(x_747, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_747, 1);
lean_inc(x_750);
lean_dec(x_747);
x_751 = x_4;
x_752 = lean_unsigned_to_nat(0u);
lean_inc(x_749);
x_753 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___spec__25(x_749, x_752, x_751);
x_754 = x_753;
x_755 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_755, 0, x_750);
lean_ctor_set(x_755, 1, x_754);
lean_ctor_set(x_755, 2, x_749);
x_756 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_756, 0, x_755);
lean_ctor_set(x_756, 1, x_6);
x_757 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_756, x_7, x_8, x_9, x_10, x_748);
return x_757;
}
else
{
uint8_t x_758; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_758 = !lean_is_exclusive(x_746);
if (x_758 == 0)
{
return x_746;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_746, 0);
x_760 = lean_ctor_get(x_746, 1);
lean_inc(x_760);
lean_inc(x_759);
lean_dec(x_746);
x_761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
return x_761;
}
}
}
else
{
lean_object* x_762; 
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_762 = l_Lean_Meta_injectionCore(x_2, x_1, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; 
x_763 = lean_ctor_get(x_762, 0);
lean_inc(x_763);
if (lean_obj_tag(x_763) == 0)
{
uint8_t x_764; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_764 = !lean_is_exclusive(x_762);
if (x_764 == 0)
{
lean_object* x_765; lean_object* x_766; 
x_765 = lean_ctor_get(x_762, 0);
lean_dec(x_765);
x_766 = lean_box(0);
lean_ctor_set(x_762, 0, x_766);
return x_762;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_762, 1);
lean_inc(x_767);
lean_dec(x_762);
x_768 = lean_box(0);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_767);
return x_769;
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_770 = lean_ctor_get(x_762, 1);
lean_inc(x_770);
lean_dec(x_762);
x_771 = lean_ctor_get(x_763, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_763, 1);
lean_inc(x_772);
lean_dec(x_763);
x_773 = lean_nat_add(x_3, x_772);
lean_dec(x_772);
x_774 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_774, 0, x_771);
lean_ctor_set(x_774, 1, x_4);
lean_ctor_set(x_774, 2, x_5);
x_775 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_775, 0, x_774);
lean_ctor_set(x_775, 1, x_6);
x_776 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_773, x_775, x_7, x_8, x_9, x_10, x_770);
lean_dec(x_773);
return x_776;
}
}
else
{
uint8_t x_777; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_777 = !lean_is_exclusive(x_762);
if (x_777 == 0)
{
return x_762;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_762, 0);
x_779 = lean_ctor_get(x_762, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_762);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
return x_780;
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
uint8_t x_781; 
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_781 = !lean_is_exclusive(x_36);
if (x_781 == 0)
{
return x_36;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_36, 0);
x_783 = lean_ctor_get(x_36, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_36);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
}
}
}
else
{
uint8_t x_785; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_785 = !lean_is_exclusive(x_33);
if (x_785 == 0)
{
return x_33;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_33, 0);
x_787 = lean_ctor_get(x_33, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_33);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
else
{
lean_object* x_789; lean_object* x_790; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
x_789 = lean_ctor_get(x_29, 1);
lean_inc(x_789);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_790 = l_Lean_Meta_clear(x_2, x_1, x_7, x_8, x_9, x_10, x_789);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
lean_dec(x_790);
x_793 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_4);
lean_ctor_set(x_793, 2, x_5);
x_794 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_6);
x_795 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_3, x_794, x_7, x_8, x_9, x_10, x_792);
return x_795;
}
else
{
uint8_t x_796; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_796 = !lean_is_exclusive(x_790);
if (x_796 == 0)
{
return x_790;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_790, 0);
x_798 = lean_ctor_get(x_790, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_790);
x_799 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
return x_799;
}
}
}
}
else
{
uint8_t x_800; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_800 = !lean_is_exclusive(x_29);
if (x_800 == 0)
{
return x_29;
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_801 = lean_ctor_get(x_29, 0);
x_802 = lean_ctor_get(x_29, 1);
lean_inc(x_802);
lean_inc(x_801);
lean_dec(x_29);
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_801);
lean_ctor_set(x_803, 1, x_802);
return x_803;
}
}
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_804 = l_Lean_Expr_appFn_x21(x_15);
x_805 = l_Lean_Expr_appFn_x21(x_804);
lean_dec(x_804);
x_806 = l_Lean_Expr_appArg_x21(x_805);
lean_dec(x_805);
x_807 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_1);
x_808 = l_Lean_mkFVar(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_809 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqOfHEqImp(x_808, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
lean_dec(x_809);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_812 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_806, x_807, x_7, x_8, x_9, x_10, x_811);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_812, 1);
lean_inc(x_814);
lean_dec(x_812);
x_815 = l_Lean_LocalDecl_userName(x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_816 = l_Lean_Meta_assert(x_2, x_815, x_813, x_810, x_7, x_8, x_9, x_10, x_814);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_819 = l_Lean_Meta_clear(x_817, x_1, x_7, x_8, x_9, x_10, x_818);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
x_822 = lean_unsigned_to_nat(1u);
x_823 = lean_nat_add(x_3, x_822);
x_824 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_824, 0, x_820);
lean_ctor_set(x_824, 1, x_4);
lean_ctor_set(x_824, 2, x_5);
x_825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_6);
x_826 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_823, x_825, x_7, x_8, x_9, x_10, x_821);
lean_dec(x_823);
return x_826;
}
else
{
uint8_t x_827; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_827 = !lean_is_exclusive(x_819);
if (x_827 == 0)
{
return x_819;
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_828 = lean_ctor_get(x_819, 0);
x_829 = lean_ctor_get(x_819, 1);
lean_inc(x_829);
lean_inc(x_828);
lean_dec(x_819);
x_830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_830, 0, x_828);
lean_ctor_set(x_830, 1, x_829);
return x_830;
}
}
}
else
{
uint8_t x_831; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_831 = !lean_is_exclusive(x_816);
if (x_831 == 0)
{
return x_816;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_832 = lean_ctor_get(x_816, 0);
x_833 = lean_ctor_get(x_816, 1);
lean_inc(x_833);
lean_inc(x_832);
lean_dec(x_816);
x_834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_834, 0, x_832);
lean_ctor_set(x_834, 1, x_833);
return x_834;
}
}
}
else
{
uint8_t x_835; 
lean_dec(x_810);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_835 = !lean_is_exclusive(x_812);
if (x_835 == 0)
{
return x_812;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_836 = lean_ctor_get(x_812, 0);
x_837 = lean_ctor_get(x_812, 1);
lean_inc(x_837);
lean_inc(x_836);
lean_dec(x_812);
x_838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_838, 0, x_836);
lean_ctor_set(x_838, 1, x_837);
return x_838;
}
}
}
else
{
uint8_t x_839; 
lean_dec(x_807);
lean_dec(x_806);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_839 = !lean_is_exclusive(x_809);
if (x_839 == 0)
{
return x_809;
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_840 = lean_ctor_get(x_809, 0);
x_841 = lean_ctor_get(x_809, 1);
lean_inc(x_841);
lean_inc(x_840);
lean_dec(x_809);
x_842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_842, 0, x_840);
lean_ctor_set(x_842, 1, x_841);
return x_842;
}
}
}
}
else
{
uint8_t x_843; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_843 = !lean_is_exclusive(x_12);
if (x_843 == 0)
{
return x_12;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_844 = lean_ctor_get(x_12, 0);
x_845 = lean_ctor_get(x_12, 1);
lean_inc(x_845);
lean_inc(x_844);
lean_dec(x_12);
x_846 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_846, 0, x_844);
lean_ctor_set(x_846, 1, x_845);
return x_846;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__2;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_31; lean_object* x_32; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_1, x_10);
x_50 = lean_st_ref_get(x_6, x_7);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = 0;
x_31 = x_55;
x_32 = x_54;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_58 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_57, x_3, x_4, x_5, x_6, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_31 = x_61;
x_32 = x_60;
goto block_49;
}
block_30:
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___boxed), 11, 6);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_11);
lean_closure_set(x_24, 3, x_16);
lean_closure_set(x_24, 4, x_17);
lean_closure_set(x_24, 5, x_14);
x_25 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_23, x_24, x_3, x_4, x_5, x_6, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
block_49:
{
if (x_31 == 0)
{
x_12 = x_32;
goto block_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_nat_add(x_11, x_10);
x_34 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__5;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_47 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_46, x_45, x_3, x_4, x_5, x_6, x_32);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_12 = x_48;
goto block_30;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_st_ref_get(x_6, x_7);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_62, 0, x_68);
return x_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_2);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_dec(x_62);
x_73 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_74 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_73, x_3, x_4, x_5, x_6, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_74, 0);
lean_dec(x_78);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
lean_ctor_set(x_74, 0, x_79);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_2);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_dec(x_74);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__7;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_90 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_73, x_90, x_3, x_4, x_5, x_6, x_84);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_2);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_2);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
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
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_16;
x_10 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_array_push(x_5, x_22);
x_4 = x_16;
x_5 = x_23;
x_10 = x_21;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_empty___closed__1;
x_10 = l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(x_1, x_2, x_2, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
x_23 = l_Lean_Meta_casesOnSuffix;
x_24 = lean_name_mk_string(x_22, x_23);
x_25 = lean_ctor_get(x_20, 4);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_List_redLength___rarg(x_25);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
x_28 = l_List_toArrayAux___rarg(x_25, x_27);
lean_inc(x_4);
x_29 = l_Lean_Meta_induction(x_3, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_31, x_28, x_4, x_18, x_19);
lean_dec(x_19);
lean_dec(x_28);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_toCasesSubgoals(x_33, x_28, x_4, x_18, x_19);
lean_dec(x_19);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
return x_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
return x_12;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_11 = l_Lean_mkFVar(x_2);
x_12 = lean_box(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed), 11, 6);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_12);
x_14 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Cases_cases___lambda__1___closed__3;
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_16, x_17, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
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
x_25 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_48 = lean_st_ref_get(x_9, x_27);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 3);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*1);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_28 = x_52;
goto block_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___closed__1;
x_55 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_54, x_6, x_7, x_8, x_9, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_28 = x_58;
goto block_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_ctor_get(x_26, 0);
lean_inc(x_60);
x_61 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_Meta_Cases_cases___lambda__1___closed__5;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_54, x_65, x_6, x_7, x_8, x_9, x_59);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_28 = x_67;
goto block_47;
}
}
block_47:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_29, x_30, x_4, x_5, x_20, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_26);
x_34 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_elimAuxIndices(x_26, x_32, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_26, 3);
lean_inc(x_37);
lean_dec(x_26);
x_38 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqs(x_37, x_35, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_35);
lean_dec(x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
else
{
uint8_t x_68; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_68 = !lean_is_exclusive(x_25);
if (x_68 == 0)
{
return x_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_25, 0);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_25);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; 
x_72 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_inductionCasesOn(x_1, x_3, x_4, x_5, x_20, x_6, x_7, x_8, x_9, x_19);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_13);
if (x_73 == 0)
{
return x_13;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_13);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_11);
if (x_77 == 0)
{
return x_11;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_11, 0);
x_79 = lean_ctor_get(x_11, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_11);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_Cases_unifyEqsAux___lambda__1___closed__2;
x_11 = lean_box(x_4);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__1___boxed), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_11);
x_13 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_Cases_cases___lambda__1(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_2418_(lean_object* x_1) {
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
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Cases___hyg_2418_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
