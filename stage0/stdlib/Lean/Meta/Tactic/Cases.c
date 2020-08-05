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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLCtx___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__23___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__22___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__18(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__21(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__7;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__3;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs(lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__20(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__25(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__5;
lean_object* l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__25___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_6__visit_x3f(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__18___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__17___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkNoConfusion___closed__8;
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__1;
extern lean_object* l_Lean_Meta_mkHEqRefl___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__17(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5;
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___closed__1;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__23(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__20___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkEqRefl___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7;
extern lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkNoConfusion___closed__5;
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__4;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__24(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__16___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10;
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
lean_object* l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__19(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__19___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__22(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__24___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_10__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_inferType(x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_6);
x_11 = l_Lean_Meta_getLevel(x_6, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_6);
x_14 = l_Lean_Meta_isExprDefEq(x_6, x_9, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_20);
x_22 = l_Lean_mkConst(x_21, x_20);
lean_inc(x_1);
lean_inc(x_6);
x_23 = l_Lean_mkApp4(x_22, x_6, x_1, x_9, x_2);
x_24 = l_Lean_Meta_mkHEqRefl___closed__1;
x_25 = l_Lean_mkConst(x_24, x_20);
x_26 = l_Lean_mkAppB(x_25, x_6, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_30);
x_32 = l_Lean_mkConst(x_31, x_30);
lean_inc(x_1);
lean_inc(x_6);
x_33 = l_Lean_mkApp4(x_32, x_6, x_1, x_9, x_2);
x_34 = l_Lean_Meta_mkHEqRefl___closed__1;
x_35 = l_Lean_mkConst(x_34, x_30);
x_36 = l_Lean_mkAppB(x_35, x_6, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_14, 0);
lean_dec(x_40);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_42);
x_44 = l_Lean_mkConst(x_43, x_42);
lean_inc(x_1);
lean_inc(x_6);
x_45 = l_Lean_mkApp3(x_44, x_6, x_1, x_2);
x_46 = l_Lean_Meta_mkEqRefl___closed__2;
x_47 = l_Lean_mkConst(x_46, x_42);
x_48 = l_Lean_mkAppB(x_47, x_6, x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_14, 0, x_49);
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_52);
x_54 = l_Lean_mkConst(x_53, x_52);
lean_inc(x_1);
lean_inc(x_6);
x_55 = l_Lean_mkApp3(x_54, x_6, x_1, x_2);
x_56 = l_Lean_Meta_mkEqRefl___closed__2;
x_57 = l_Lean_mkConst(x_56, x_52);
x_58 = l_Lean_mkAppB(x_57, x_6, x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
return x_14;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_11);
if (x_65 == 0)
{
return x_11;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_8);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
return x_5;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get(x_5, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_5);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = lean_array_push(x_2, x_8);
x_14 = lean_array_push(x_3, x_4);
x_15 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(x_5, x_6, x_7, x_12, x_13, x_14, x_9, x_10);
return x_15;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_apply_4(x_3, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_Inhabited;
x_13 = lean_array_get(x_12, x_1, x_4);
x_14 = lean_array_get(x_12, x_2, x_4);
lean_inc(x_7);
x_15 = l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(x_13, x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
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
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_6);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_1);
lean_closure_set(x_20, 5, x_2);
lean_closure_set(x_20, 6, x_3);
x_21 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2;
x_22 = 0;
x_23 = l_Lean_Meta_withLocalDecl___rarg(x_21, x_18, x_22, x_20, x_7, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_6, x_7, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_1, x_10);
lean_inc(x_2);
x_14 = l_Lean_Meta_getMVarType(x_2, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_Meta_getMVarTag(x_2, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_13);
x_20 = l_Lean_Meta_mkForall(x_13, x_15, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_3);
lean_inc(x_11);
x_25 = l_Lean_Meta_mkForall(x_24, x_21, x_11, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_4);
x_28 = l_Lean_Meta_mkForall(x_4, x_26, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 2;
x_32 = l_Lean_Meta_mkFreshExprMVarAt(x_5, x_6, x_29, x_18, x_31, x_11, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_33);
x_36 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_7, x_7, x_35, x_33);
x_37 = l_Lean_mkApp(x_36, x_8);
x_38 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_9, x_9, x_35, x_37);
x_39 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
x_40 = lean_array_get_size(x_4);
lean_dec(x_4);
x_41 = lean_box(0);
x_42 = l_Lean_Meta_assignExprMVar(x_2, x_38, x_11, x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_44, x_39, x_40, x_41, x_11, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_Meta_intro1(x_49, x_44, x_11, x_47);
lean_dec(x_11);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_array_get_size(x_13);
lean_dec(x_13);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_array_get_size(x_13);
lean_dec(x_13);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_48);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_13);
x_64 = !lean_is_exclusive(x_50);
if (x_64 == 0)
{
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_50);
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
lean_dec(x_13);
lean_dec(x_11);
x_68 = !lean_is_exclusive(x_45);
if (x_68 == 0)
{
return x_45;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_45, 0);
x_70 = lean_ctor_get(x_45, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_45);
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
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_11);
x_72 = !lean_is_exclusive(x_42);
if (x_72 == 0)
{
return x_42;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_42, 0);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_42);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_28);
if (x_76 == 0)
{
return x_28;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_28, 0);
x_78 = lean_ctor_get(x_28, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_25);
if (x_80 == 0)
{
return x_25;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_25, 0);
x_82 = lean_ctor_get(x_25, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_25);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_20);
if (x_84 == 0)
{
return x_20;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_20, 0);
x_86 = lean_ctor_get(x_20, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_17);
if (x_88 == 0)
{
return x_17;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_17, 0);
x_90 = lean_ctor_get(x_17, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_17);
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
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_14);
if (x_92 == 0)
{
return x_14;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_14, 0);
x_94 = lean_ctor_get(x_14, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_14);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_LocalDecl_toExpr(x_1);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_12);
x_13 = l___private_Lean_Meta_Tactic_Cases_1__mkEqAndProof(x_12, x_2, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
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
x_18 = lean_array_push(x_9, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed), 12, 9);
lean_closure_set(x_19, 0, x_8);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_7);
lean_closure_set(x_19, 7, x_12);
lean_closure_set(x_19, 8, x_18);
x_20 = l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2;
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___rarg(x_20, x_16, x_21, x_19, x_10, x_15);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed), 11, 7);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
x_11 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqs___rarg(x_6, x_3, x_10, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_7, x_7, x_11, x_1);
x_13 = l_Lean_LocalDecl_userName(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3), 9, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
x_15 = 0;
x_16 = l_Lean_Meta_withLocalDecl___rarg(x_13, x_12, x_15, x_14, x_9, x_10);
return x_16;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("indexed inductive type expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed inductive datatype");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_7)) {
case 4:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_environment_find(x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_mkNoConfusion___closed__8;
x_15 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_14, x_10, x_11);
lean_dec(x_10);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = lean_array_get_size(x_8);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_nat_add(x_18, x_22);
x_24 = lean_nat_dec_eq(x_21, x_23);
lean_dec(x_23);
x_25 = lean_nat_sub(x_21, x_18);
lean_dec(x_18);
x_26 = l_Array_extract___rarg(x_8, x_25, x_21);
lean_dec(x_21);
x_27 = l_Array_extract___rarg(x_8, x_19, x_22);
lean_dec(x_22);
lean_dec(x_8);
x_28 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_19, x_7);
lean_dec(x_27);
if (x_24 == 0)
{
uint8_t x_54; 
x_54 = 0;
x_29 = x_54;
goto block_53;
}
else
{
uint8_t x_55; 
x_55 = 1;
x_29 = x_55;
goto block_53;
}
block_53:
{
lean_object* x_30; 
if (x_20 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_41 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_41, x_10, x_11);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
if (x_29 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_47 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_47, x_10, x_11);
lean_dec(x_10);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_dec(x_5);
x_30 = x_11;
goto block_40;
}
}
block_40:
{
lean_object* x_31; 
lean_inc(x_10);
lean_inc(x_28);
x_31 = l_Lean_Meta_inferType(x_28, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed), 10, 6);
lean_closure_set(x_34, 0, x_28);
lean_closure_set(x_34, 1, x_6);
lean_closure_set(x_34, 2, x_1);
lean_closure_set(x_34, 3, x_2);
lean_closure_set(x_34, 4, x_3);
lean_closure_set(x_34, 5, x_26);
x_35 = l_Lean_Meta_forallTelescopeReducing___rarg(x_32, x_34, x_10, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
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
lean_object* x_56; lean_object* x_57; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_56 = l_Lean_Meta_mkNoConfusion___closed__8;
x_57 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_56, x_10, x_11);
lean_dec(x_10);
return x_57;
}
}
}
case 5:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_7, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_dec(x_7);
x_60 = lean_array_set(x_8, x_9, x_59);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_9, x_61);
lean_dec(x_9);
x_7 = x_58;
x_8 = x_60;
x_9 = x_62;
goto _start;
}
default: 
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = l_Lean_Meta_mkNoConfusion___closed__8;
x_65 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_64, x_10, x_11);
lean_dec(x_10);
return x_65;
}
}
}
}
lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("generalizeIndices");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Meta_checkNotAssigned(x_1, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
x_11 = l_Lean_Meta_getLocalDecl(x_2, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_inc(x_4);
x_15 = l_Lean_Meta_whnf(x_14, x_4, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux___main(x_16, x_18);
x_20 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_24 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(x_1, x_3, x_6, x_7, x_8, x_12, x_16, x_21, x_23, x_4, x_17);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l_Lean_Meta_generalizeIndices___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getLCtx___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_generalizeIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_generalizeIndices___lambda__1), 5, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Meta_generalizeIndices___closed__1;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_withLocalContext___rarg(x_11, x_12, x_7, x_3, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_generalizeIndices(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_1);
x_9 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_get_size(x_4);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_14, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_casesOnSuffix___closed__1;
x_24 = lean_name_mk_string(x_22, x_23);
x_25 = lean_environment_find(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_13, 4);
lean_inc(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_List_lengthAux___main___rarg(x_31, x_32);
lean_dec(x_31);
x_34 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
x_35 = l_Array_extract___rarg(x_4, x_34, x_14);
lean_dec(x_14);
x_36 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_2);
lean_ctor_set(x_36, 4, x_3);
lean_ctor_set(x_36, 5, x_4);
lean_ctor_set(x_36, 6, x_35);
lean_ctor_set(x_25, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_25);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
lean_dec(x_25);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_13, 4);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_List_lengthAux___main___rarg(x_42, x_43);
lean_dec(x_42);
x_45 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
x_46 = l_Array_extract___rarg(x_4, x_45, x_14);
lean_dec(x_14);
x_47 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_2);
lean_ctor_set(x_47, 4, x_3);
lean_ctor_set(x_47, 5, x_4);
lean_ctor_set(x_47, 6, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_7);
return x_51;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
}
case 5:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
lean_dec(x_3);
x_56 = lean_array_set(x_4, x_5, x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_5, x_57);
lean_dec(x_5);
x_3 = x_54;
x_4 = x_56;
x_5 = x_58;
goto _start;
}
default: 
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_4);
x_6 = l_Lean_Environment_contains(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_4);
x_10 = l_Lean_Environment_contains(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_2);
x_13 = l_Lean_Meta_getLocalDecl(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_type(x_14);
lean_inc(x_2);
x_17 = l_Lean_Meta_whnf(x_16, x_2, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_20);
x_22 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
x_26 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(x_4, x_14, x_18, x_23, x_25, x_2, x_19);
lean_dec(x_2);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
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
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_10 = l_Lean_Expr_Inhabited;
x_11 = lean_array_get(x_10, x_1, x_2);
x_12 = lean_array_get(x_10, x_1, x_9);
lean_dec(x_9);
x_13 = lean_expr_eqv(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = 0;
return x_16;
}
}
}
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
lean_inc(x_8);
x_9 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(x_1, x_8, x_8, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_7);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_5);
return x_10;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(x_1, x_2, x_3, x_10);
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
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
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
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(x_1, x_2, x_3, x_10);
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
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
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
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(x_1, x_2, x_3, x_10);
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
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
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
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(x_1, x_2, x_3, x_10);
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
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
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
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(x_1, x_2, x_3, x_10);
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
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
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
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(x_1, x_2, x_3, x_10);
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
lean_dec(x_7);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(x_1, x_2, x_3, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l___private_Lean_MetavarContext_6__visit_x3f(x_24, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_5 = x_24;
x_6 = x_32;
goto _start;
}
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
lean_inc(x_35);
x_36 = l___private_Lean_MetavarContext_6__visit_x3f(x_35, x_6);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Expr_isApp(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_34);
x_41 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_5 = x_34;
x_6 = x_48;
goto _start;
}
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
lean_inc(x_4);
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_35, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_Expr_isApp(x_34);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_34);
x_57 = l___private_Lean_MetavarContext_6__visit_x3f(x_34, x_55);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_5 = x_34;
x_6 = x_64;
goto _start;
}
}
else
{
x_5 = x_34;
x_6 = x_55;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
lean_dec(x_5);
lean_inc(x_71);
x_73 = l___private_Lean_MetavarContext_6__visit_x3f(x_71, x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_72);
x_77 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_5 = x_72;
x_6 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_dec(x_73);
lean_inc(x_4);
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_71, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_88);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_72);
x_91 = l___private_Lean_MetavarContext_6__visit_x3f(x_72, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_72);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_92);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_5 = x_72;
x_6 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_87, 0);
lean_dec(x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_5, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_dec(x_5);
lean_inc(x_104);
x_106 = l___private_Lean_MetavarContext_6__visit_x3f(x_104, x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_104);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
lean_inc(x_105);
x_110 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_105);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
return x_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_5 = x_105;
x_6 = x_117;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_dec(x_106);
lean_inc(x_4);
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_104, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_121);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_105);
x_124 = l___private_Lean_MetavarContext_6__visit_x3f(x_105, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_105);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_124);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_dec(x_128);
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_5 = x_105;
x_6 = x_131;
goto _start;
}
}
else
{
uint8_t x_133; 
lean_dec(x_105);
lean_dec(x_4);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_120, 0);
lean_dec(x_134);
return x_120;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_5, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 3);
lean_inc(x_139);
lean_dec(x_5);
lean_inc(x_137);
x_176 = l___private_Lean_MetavarContext_6__visit_x3f(x_137, x_6);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_137);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_unbox(x_177);
lean_dec(x_177);
x_140 = x_180;
x_141 = x_179;
goto block_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_177);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
lean_inc(x_4);
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_137, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unbox(x_183);
lean_dec(x_183);
x_140 = x_185;
x_141 = x_184;
goto block_175;
}
block_175:
{
if (x_140 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_inc(x_138);
x_142 = l___private_Lean_MetavarContext_6__visit_x3f(x_138, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_138);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
lean_inc(x_139);
x_146 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_139);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_dec(x_147);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_5 = x_139;
x_6 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_142, 1);
lean_inc(x_155);
lean_dec(x_142);
lean_inc(x_4);
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_138, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
lean_inc(x_139);
x_160 = l___private_Lean_MetavarContext_6__visit_x3f(x_139, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
uint8_t x_163; 
lean_dec(x_139);
lean_dec(x_4);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_160, 0);
lean_dec(x_164);
return x_160;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_161);
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_5 = x_139;
x_6 = x_167;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_139);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_156);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_156, 0);
lean_dec(x_170);
return x_156;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_156, 1);
lean_inc(x_171);
lean_dec(x_156);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_157);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_4);
x_173 = lean_box(x_140);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_141);
return x_174;
}
}
}
case 10:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_5, 1);
lean_inc(x_186);
lean_dec(x_5);
lean_inc(x_186);
x_187 = l___private_Lean_MetavarContext_6__visit_x3f(x_186, x_6);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
lean_dec(x_4);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_187, 0);
lean_dec(x_191);
return x_187;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_188);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
lean_dec(x_187);
x_5 = x_186;
x_6 = x_194;
goto _start;
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_5, 2);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_196);
x_197 = l___private_Lean_MetavarContext_6__visit_x3f(x_196, x_6);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_196);
lean_dec(x_4);
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_197, 0);
lean_dec(x_201);
return x_197;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_198);
x_204 = lean_ctor_get(x_197, 1);
lean_inc(x_204);
lean_dec(x_197);
x_5 = x_196;
x_6 = x_204;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_11);
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
lean_dec(x_8);
lean_dec(x_4);
return x_12;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; 
x_11 = lean_array_fget(x_6, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_LocalDecl_fvarId(x_15);
x_17 = lean_ctor_get(x_1, 3);
x_18 = l_Lean_LocalDecl_fvarId(x_17);
x_19 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(x_1, x_16, x_2, x_3, x_20);
lean_dec(x_16);
if (x_21 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 3);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Expr_hasFVar(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasMVar(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_4);
x_25 = 1;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_27 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_22, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_4);
x_30 = 1;
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_8 = x_32;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_35 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_22, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_4);
x_38 = 1;
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_8, x_39);
lean_dec(x_8);
x_8 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_67; 
x_42 = lean_ctor_get(x_15, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_15, 4);
lean_inc(x_43);
lean_dec(x_15);
x_67 = l_Lean_Expr_hasFVar(x_42);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_hasMVar(x_42);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; 
lean_dec(x_42);
x_69 = 0;
x_70 = l_Std_HashSet_Inhabited___closed__1;
x_44 = x_69;
x_45 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_42, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_44 = x_75;
x_45 = x_74;
goto block_66;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_77 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_42, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_44 = x_80;
x_45 = x_79;
goto block_66;
}
block_66:
{
if (x_44 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_hasFVar(x_43);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasMVar(x_43);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_4);
x_48 = 1;
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_43, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_4);
x_52 = 1;
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_8, x_53);
lean_dec(x_8);
x_8 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_4);
x_56 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_43, x_45);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_4);
x_59 = 1;
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
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
lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_43);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_8, x_63);
lean_dec(x_8);
x_8 = x_64;
goto _start;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_15);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_8, x_81);
lean_dec(x_8);
x_8 = x_82;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_16);
lean_dec(x_15);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_8, x_84);
lean_dec(x_8);
x_8 = x_85;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(x_1, x_2, x_3, x_4, x_6, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_10, x_10, x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; 
x_11 = lean_array_fget(x_6, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_LocalDecl_fvarId(x_15);
x_17 = lean_ctor_get(x_1, 3);
x_18 = l_Lean_LocalDecl_fvarId(x_17);
x_19 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(x_1, x_16, x_2, x_3, x_20);
lean_dec(x_16);
if (x_21 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 3);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Expr_hasFVar(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasMVar(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_4);
x_25 = 1;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_27 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_22, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_4);
x_30 = 1;
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_8 = x_32;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_35 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_22, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_4);
x_38 = 1;
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_8, x_39);
lean_dec(x_8);
x_8 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_67; 
x_42 = lean_ctor_get(x_15, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_15, 4);
lean_inc(x_43);
lean_dec(x_15);
x_67 = l_Lean_Expr_hasFVar(x_42);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_hasMVar(x_42);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; 
lean_dec(x_42);
x_69 = 0;
x_70 = l_Std_HashSet_Inhabited___closed__1;
x_44 = x_69;
x_45 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_72 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_42, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_44 = x_75;
x_45 = x_74;
goto block_66;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = l_Std_HashSet_Inhabited___closed__1;
lean_inc(x_4);
x_77 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_42, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_44 = x_80;
x_45 = x_79;
goto block_66;
}
block_66:
{
if (x_44 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_hasFVar(x_43);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasMVar(x_43);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_4);
x_48 = 1;
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_4);
x_49 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_43, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_4);
x_52 = 1;
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_8, x_53);
lean_dec(x_8);
x_8 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_4);
x_56 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_43, x_45);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_4);
x_59 = 1;
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
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
lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_43);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_8, x_63);
lean_dec(x_8);
x_8 = x_64;
goto _start;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_15);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_8, x_81);
lean_dec(x_8);
x_8 = x_82;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_16);
lean_dec(x_15);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_8, x_84);
lean_dec(x_8);
x_8 = x_85;
goto _start;
}
}
}
}
}
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_4);
x_7 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 6);
x_5 = l_Array_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(x_1, x_4, x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_6);
x_9 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(x_4, x_6, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
x_13 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(x_1, x_4, x_6, x_11, x_12);
lean_dec(x_6);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__20(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__19(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__26(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__25(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__32(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__31(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__40(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__38(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__37(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__44(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___spec__42(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_10);
x_16 = l_Lean_Meta_FVarSubst_get(x_15, x_10);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_6);
x_18 = l_Lean_Meta_clear(x_13, x_17, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_4, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_4, 2, x_25);
lean_ctor_set(x_4, 0, x_23);
x_3 = x_12;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_10, x_15);
lean_dec(x_10);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_29);
x_3 = x_12;
x_4 = x_30;
x_6 = x_28;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_6, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 5);
lean_inc(x_35);
lean_dec(x_6);
x_36 = l_Lean_Meta_restore(x_33, x_34, x_35, x_5, x_32);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_3 = x_12;
x_6 = x_37;
goto _start;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
x_3 = x_12;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = x_4;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_array_fget(x_4, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_4, x_3, x_12);
x_14 = x_11;
x_15 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(x_1, x_2, x_12, x_14, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_13, x_3, x_20);
lean_dec(x_3);
x_3 = x_19;
x_4 = x_21;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = x_2;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2___boxed), 6, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
x_9 = x_8;
x_10 = lean_apply_2(x_9, x_3, x_4);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Name_inhabited;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = x_13;
x_17 = lean_array_fset(x_9, x_2, x_16);
lean_dec(x_2);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = x_1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(x_2, x_4, x_3);
x_6 = x_5;
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cases");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_LocalDecl_type(x_6);
x_10 = l_Lean_Expr_heq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_9, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_eq_x3f___closed__2;
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Expr_isAppOfArity___main(x_9, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2;
x_17 = l_Lean_Meta_mkNoConfusion___closed__5;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_16, x_1, x_17, x_7, x_8);
lean_dec(x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Expr_appFn_x21(x_9);
x_20 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_21 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_21);
lean_inc(x_20);
x_22 = l_Lean_Meta_isExprDefEq(x_20, x_21, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_7);
lean_inc(x_20);
x_26 = l_Lean_Meta_whnf(x_20, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_21);
x_29 = l_Lean_Meta_whnf(x_21, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_expr_eqv(x_27, x_20);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_inc(x_2);
x_33 = l_Lean_mkFVar(x_2);
lean_inc(x_7);
x_34 = l_Lean_Meta_mkEq(x_27, x_30, x_7, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_LocalDecl_userName(x_6);
x_38 = l_Lean_Meta_assert(x_1, x_37, x_35, x_33, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_clear(x_39, x_2, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_3, x_44);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 2);
lean_inc(x_47);
lean_dec(x_4);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
x_50 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_45, x_49, x_7, x_43);
lean_dec(x_7);
lean_dec(x_45);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
return x_38;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_38);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_34);
if (x_59 == 0)
{
return x_34;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_34, 0);
x_61 = lean_ctor_get(x_34, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_34);
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
x_63 = lean_expr_eqv(x_30, x_21);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_inc(x_2);
x_64 = l_Lean_mkFVar(x_2);
lean_inc(x_7);
x_65 = l_Lean_Meta_mkEq(x_27, x_30, x_7, x_31);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_LocalDecl_userName(x_6);
x_69 = l_Lean_Meta_assert(x_1, x_68, x_66, x_64, x_7, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_clear(x_70, x_2, x_7, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_3, x_75);
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_4, 2);
lean_inc(x_78);
lean_dec(x_4);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_5);
x_81 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_76, x_80, x_7, x_74);
lean_dec(x_7);
lean_dec(x_76);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_72);
if (x_82 == 0)
{
return x_72;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_72, 0);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_72);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_69);
if (x_86 == 0)
{
return x_69;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_69, 0);
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_69);
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
lean_dec(x_64);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_65);
if (x_90 == 0)
{
return x_65;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_65, 0);
x_92 = lean_ctor_get(x_65, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_65);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_27);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; 
lean_dec(x_21);
x_94 = lean_ctor_get(x_4, 2);
lean_inc(x_94);
x_95 = 1;
x_96 = l_Lean_Meta_substCore(x_1, x_2, x_95, x_94, x_7, x_31);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
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
x_101 = lean_ctor_get(x_4, 1);
lean_inc(x_101);
lean_dec(x_4);
x_102 = x_101;
x_103 = lean_unsigned_to_nat(0u);
x_104 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(x_99, x_103, x_102);
x_105 = x_104;
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_99);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_5);
x_108 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_107, x_7, x_98);
lean_dec(x_7);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_96);
if (x_109 == 0)
{
return x_96;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_96, 0);
x_111 = lean_ctor_get(x_96, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_96);
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
lean_dec(x_21);
x_113 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_115 = !lean_is_exclusive(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 0);
lean_dec(x_116);
x_117 = lean_box(0);
lean_ctor_set(x_113, 0, x_117);
return x_113;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_dec(x_113);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
lean_dec(x_113);
x_122 = lean_ctor_get(x_114, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_114, 1);
lean_inc(x_123);
lean_dec(x_114);
x_124 = lean_nat_add(x_3, x_123);
lean_dec(x_123);
x_125 = lean_ctor_get(x_4, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_4, 2);
lean_inc(x_126);
lean_dec(x_4);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_125);
lean_ctor_set(x_127, 2, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_5);
x_129 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_124, x_128, x_7, x_121);
lean_dec(x_7);
lean_dec(x_124);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_130 = !lean_is_exclusive(x_113);
if (x_130 == 0)
{
return x_113;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_113, 0);
x_132 = lean_ctor_get(x_113, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_113);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
case 1:
{
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; 
lean_dec(x_21);
lean_dec(x_20);
x_134 = lean_ctor_get(x_4, 2);
lean_inc(x_134);
x_135 = lean_unbox(x_23);
lean_dec(x_23);
x_136 = l_Lean_Meta_substCore(x_1, x_2, x_135, x_134, x_7, x_31);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_ctor_get(x_4, 1);
lean_inc(x_141);
lean_dec(x_4);
x_142 = x_141;
x_143 = lean_unsigned_to_nat(0u);
x_144 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(x_139, x_143, x_142);
x_145 = x_144;
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_139);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_5);
x_148 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_147, x_7, x_138);
lean_dec(x_7);
return x_148;
}
else
{
uint8_t x_149; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_136);
if (x_149 == 0)
{
return x_136;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_136, 0);
x_151 = lean_ctor_get(x_136, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_136);
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
lean_dec(x_23);
x_153 = lean_ctor_get(x_20, 0);
lean_inc(x_153);
lean_dec(x_20);
x_154 = lean_ctor_get(x_21, 0);
lean_inc(x_154);
lean_dec(x_21);
lean_inc(x_7);
x_155 = l_Lean_Meta_getLocalDecl(x_153, x_7, x_31);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_7);
x_158 = l_Lean_Meta_getLocalDecl(x_154, x_7, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
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
x_164 = lean_ctor_get(x_4, 2);
lean_inc(x_164);
x_165 = l_Lean_Meta_substCore(x_1, x_2, x_163, x_164, x_7, x_160);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
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
x_170 = lean_ctor_get(x_4, 1);
lean_inc(x_170);
lean_dec(x_4);
x_171 = x_170;
x_172 = lean_unsigned_to_nat(0u);
x_173 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(x_168, x_172, x_171);
x_174 = x_173;
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set(x_175, 2, x_168);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_5);
x_177 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_176, x_7, x_167);
lean_dec(x_7);
return x_177;
}
else
{
uint8_t x_178; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_178 = !lean_is_exclusive(x_165);
if (x_178 == 0)
{
return x_165;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_165, 0);
x_180 = lean_ctor_get(x_165, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_165);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_156);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_158);
if (x_182 == 0)
{
return x_158;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_158, 0);
x_184 = lean_ctor_get(x_158, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_158);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_154);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_155);
if (x_186 == 0)
{
return x_155;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_155, 0);
x_188 = lean_ctor_get(x_155, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_155);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
case 2:
{
lean_object* x_190; uint8_t x_191; lean_object* x_192; 
lean_dec(x_21);
lean_dec(x_20);
x_190 = lean_ctor_get(x_4, 2);
lean_inc(x_190);
x_191 = lean_unbox(x_23);
lean_dec(x_23);
x_192 = l_Lean_Meta_substCore(x_1, x_2, x_191, x_190, x_7, x_31);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_ctor_get(x_4, 1);
lean_inc(x_197);
lean_dec(x_4);
x_198 = x_197;
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(x_195, x_199, x_198);
x_201 = x_200;
x_202 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_202, 0, x_196);
lean_ctor_set(x_202, 1, x_201);
lean_ctor_set(x_202, 2, x_195);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_5);
x_204 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_203, x_7, x_194);
lean_dec(x_7);
return x_204;
}
else
{
uint8_t x_205; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_205 = !lean_is_exclusive(x_192);
if (x_205 == 0)
{
return x_192;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_192, 0);
x_207 = lean_ctor_get(x_192, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_192);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
case 3:
{
lean_object* x_209; uint8_t x_210; lean_object* x_211; 
lean_dec(x_21);
lean_dec(x_20);
x_209 = lean_ctor_get(x_4, 2);
lean_inc(x_209);
x_210 = lean_unbox(x_23);
lean_dec(x_23);
x_211 = l_Lean_Meta_substCore(x_1, x_2, x_210, x_209, x_7, x_31);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
x_216 = lean_ctor_get(x_4, 1);
lean_inc(x_216);
lean_dec(x_4);
x_217 = x_216;
x_218 = lean_unsigned_to_nat(0u);
x_219 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(x_214, x_218, x_217);
x_220 = x_219;
x_221 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_221, 0, x_215);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_214);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_5);
x_223 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_222, x_7, x_213);
lean_dec(x_7);
return x_223;
}
else
{
uint8_t x_224; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_224 = !lean_is_exclusive(x_211);
if (x_224 == 0)
{
return x_211;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_211, 0);
x_226 = lean_ctor_get(x_211, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_211);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
case 4:
{
lean_object* x_228; uint8_t x_229; lean_object* x_230; 
lean_dec(x_21);
lean_dec(x_20);
x_228 = lean_ctor_get(x_4, 2);
lean_inc(x_228);
x_229 = lean_unbox(x_23);
lean_dec(x_23);
x_230 = l_Lean_Meta_substCore(x_1, x_2, x_229, x_228, x_7, x_31);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
x_235 = lean_ctor_get(x_4, 1);
lean_inc(x_235);
lean_dec(x_4);
x_236 = x_235;
x_237 = lean_unsigned_to_nat(0u);
x_238 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(x_233, x_237, x_236);
x_239 = x_238;
x_240 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_240, 0, x_234);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_240, 2, x_233);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_5);
x_242 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_241, x_7, x_232);
lean_dec(x_7);
return x_242;
}
else
{
uint8_t x_243; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_243 = !lean_is_exclusive(x_230);
if (x_243 == 0)
{
return x_230;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_230, 0);
x_245 = lean_ctor_get(x_230, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_230);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
case 5:
{
lean_object* x_247; uint8_t x_248; lean_object* x_249; 
lean_dec(x_21);
lean_dec(x_20);
x_247 = lean_ctor_get(x_4, 2);
lean_inc(x_247);
x_248 = lean_unbox(x_23);
lean_dec(x_23);
x_249 = l_Lean_Meta_substCore(x_1, x_2, x_248, x_247, x_7, x_31);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
lean_dec(x_250);
x_254 = lean_ctor_get(x_4, 1);
lean_inc(x_254);
lean_dec(x_4);
x_255 = x_254;
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(x_252, x_256, x_255);
x_258 = x_257;
x_259 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_259, 2, x_252);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_5);
x_261 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_260, x_7, x_251);
lean_dec(x_7);
return x_261;
}
else
{
uint8_t x_262; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_262 = !lean_is_exclusive(x_249);
if (x_262 == 0)
{
return x_249;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_249, 0);
x_264 = lean_ctor_get(x_249, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_249);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
case 6:
{
lean_object* x_266; uint8_t x_267; lean_object* x_268; 
lean_dec(x_21);
lean_dec(x_20);
x_266 = lean_ctor_get(x_4, 2);
lean_inc(x_266);
x_267 = lean_unbox(x_23);
lean_dec(x_23);
x_268 = l_Lean_Meta_substCore(x_1, x_2, x_267, x_266, x_7, x_31);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_ctor_get(x_4, 1);
lean_inc(x_273);
lean_dec(x_4);
x_274 = x_273;
x_275 = lean_unsigned_to_nat(0u);
x_276 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(x_271, x_275, x_274);
x_277 = x_276;
x_278 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_278, 0, x_272);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_278, 2, x_271);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_5);
x_280 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_279, x_7, x_270);
lean_dec(x_7);
return x_280;
}
else
{
uint8_t x_281; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_281 = !lean_is_exclusive(x_268);
if (x_281 == 0)
{
return x_268;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_268, 0);
x_283 = lean_ctor_get(x_268, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_268);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
case 7:
{
lean_object* x_285; uint8_t x_286; lean_object* x_287; 
lean_dec(x_21);
lean_dec(x_20);
x_285 = lean_ctor_get(x_4, 2);
lean_inc(x_285);
x_286 = lean_unbox(x_23);
lean_dec(x_23);
x_287 = l_Lean_Meta_substCore(x_1, x_2, x_286, x_285, x_7, x_31);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_ctor_get(x_4, 1);
lean_inc(x_292);
lean_dec(x_4);
x_293 = x_292;
x_294 = lean_unsigned_to_nat(0u);
x_295 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(x_290, x_294, x_293);
x_296 = x_295;
x_297 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_297, 0, x_291);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set(x_297, 2, x_290);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_5);
x_299 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_298, x_7, x_289);
lean_dec(x_7);
return x_299;
}
else
{
uint8_t x_300; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_300 = !lean_is_exclusive(x_287);
if (x_300 == 0)
{
return x_287;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_287, 0);
x_302 = lean_ctor_get(x_287, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_287);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
case 8:
{
lean_object* x_304; uint8_t x_305; lean_object* x_306; 
lean_dec(x_21);
lean_dec(x_20);
x_304 = lean_ctor_get(x_4, 2);
lean_inc(x_304);
x_305 = lean_unbox(x_23);
lean_dec(x_23);
x_306 = l_Lean_Meta_substCore(x_1, x_2, x_305, x_304, x_7, x_31);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_ctor_get(x_4, 1);
lean_inc(x_311);
lean_dec(x_4);
x_312 = x_311;
x_313 = lean_unsigned_to_nat(0u);
x_314 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(x_309, x_313, x_312);
x_315 = x_314;
x_316 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_316, 0, x_310);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set(x_316, 2, x_309);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_5);
x_318 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_317, x_7, x_308);
lean_dec(x_7);
return x_318;
}
else
{
uint8_t x_319; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_319 = !lean_is_exclusive(x_306);
if (x_319 == 0)
{
return x_306;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_306, 0);
x_321 = lean_ctor_get(x_306, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_306);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
case 9:
{
lean_object* x_323; uint8_t x_324; lean_object* x_325; 
lean_dec(x_21);
lean_dec(x_20);
x_323 = lean_ctor_get(x_4, 2);
lean_inc(x_323);
x_324 = lean_unbox(x_23);
lean_dec(x_23);
x_325 = l_Lean_Meta_substCore(x_1, x_2, x_324, x_323, x_7, x_31);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
lean_dec(x_326);
x_330 = lean_ctor_get(x_4, 1);
lean_inc(x_330);
lean_dec(x_4);
x_331 = x_330;
x_332 = lean_unsigned_to_nat(0u);
x_333 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(x_328, x_332, x_331);
x_334 = x_333;
x_335 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_335, 0, x_329);
lean_ctor_set(x_335, 1, x_334);
lean_ctor_set(x_335, 2, x_328);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_5);
x_337 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_336, x_7, x_327);
lean_dec(x_7);
return x_337;
}
else
{
uint8_t x_338; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_338 = !lean_is_exclusive(x_325);
if (x_338 == 0)
{
return x_325;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_325, 0);
x_340 = lean_ctor_get(x_325, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_325);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
case 10:
{
lean_object* x_342; uint8_t x_343; lean_object* x_344; 
lean_dec(x_21);
lean_dec(x_20);
x_342 = lean_ctor_get(x_4, 2);
lean_inc(x_342);
x_343 = lean_unbox(x_23);
lean_dec(x_23);
x_344 = l_Lean_Meta_substCore(x_1, x_2, x_343, x_342, x_7, x_31);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
lean_dec(x_345);
x_349 = lean_ctor_get(x_4, 1);
lean_inc(x_349);
lean_dec(x_4);
x_350 = x_349;
x_351 = lean_unsigned_to_nat(0u);
x_352 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(x_347, x_351, x_350);
x_353 = x_352;
x_354 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_354, 0, x_348);
lean_ctor_set(x_354, 1, x_353);
lean_ctor_set(x_354, 2, x_347);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_5);
x_356 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_355, x_7, x_346);
lean_dec(x_7);
return x_356;
}
else
{
uint8_t x_357; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_357 = !lean_is_exclusive(x_344);
if (x_357 == 0)
{
return x_344;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_344, 0);
x_359 = lean_ctor_get(x_344, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_344);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
case 11:
{
lean_object* x_361; uint8_t x_362; lean_object* x_363; 
lean_dec(x_21);
lean_dec(x_20);
x_361 = lean_ctor_get(x_4, 2);
lean_inc(x_361);
x_362 = lean_unbox(x_23);
lean_dec(x_23);
x_363 = l_Lean_Meta_substCore(x_1, x_2, x_362, x_361, x_7, x_31);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_ctor_get(x_4, 1);
lean_inc(x_368);
lean_dec(x_4);
x_369 = x_368;
x_370 = lean_unsigned_to_nat(0u);
x_371 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(x_366, x_370, x_369);
x_372 = x_371;
x_373 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_373, 0, x_367);
lean_ctor_set(x_373, 1, x_372);
lean_ctor_set(x_373, 2, x_366);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_5);
x_375 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_374, x_7, x_365);
lean_dec(x_7);
return x_375;
}
else
{
uint8_t x_376; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_376 = !lean_is_exclusive(x_363);
if (x_376 == 0)
{
return x_363;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_363, 0);
x_378 = lean_ctor_get(x_363, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_363);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
default: 
{
lean_object* x_380; uint8_t x_381; lean_object* x_382; 
lean_dec(x_21);
lean_dec(x_20);
x_380 = lean_ctor_get(x_4, 2);
lean_inc(x_380);
x_381 = lean_unbox(x_23);
lean_dec(x_23);
x_382 = l_Lean_Meta_substCore(x_1, x_2, x_381, x_380, x_7, x_31);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_387 = lean_ctor_get(x_4, 1);
lean_inc(x_387);
lean_dec(x_4);
x_388 = x_387;
x_389 = lean_unsigned_to_nat(0u);
x_390 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(x_385, x_389, x_388);
x_391 = x_390;
x_392 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_392, 0, x_386);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_392, 2, x_385);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_5);
x_394 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_393, x_7, x_384);
lean_dec(x_7);
return x_394;
}
else
{
uint8_t x_395; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_395 = !lean_is_exclusive(x_382);
if (x_395 == 0)
{
return x_382;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_382, 0);
x_397 = lean_ctor_get(x_382, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_382);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
}
}
case 2:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_399; uint8_t x_400; lean_object* x_401; 
lean_dec(x_21);
x_399 = lean_ctor_get(x_4, 2);
lean_inc(x_399);
x_400 = 1;
x_401 = l_Lean_Meta_substCore(x_1, x_2, x_400, x_399, x_7, x_31);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_dec(x_402);
x_406 = lean_ctor_get(x_4, 1);
lean_inc(x_406);
lean_dec(x_4);
x_407 = x_406;
x_408 = lean_unsigned_to_nat(0u);
x_409 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__15(x_404, x_408, x_407);
x_410 = x_409;
x_411 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_411, 0, x_405);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_411, 2, x_404);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_5);
x_413 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_412, x_7, x_403);
lean_dec(x_7);
return x_413;
}
else
{
uint8_t x_414; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_414 = !lean_is_exclusive(x_401);
if (x_414 == 0)
{
return x_401;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_401, 0);
x_416 = lean_ctor_get(x_401, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_401);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
else
{
lean_object* x_418; 
lean_dec(x_21);
x_418 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
if (lean_obj_tag(x_419) == 0)
{
uint8_t x_420; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_420 = !lean_is_exclusive(x_418);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_418, 0);
lean_dec(x_421);
x_422 = lean_box(0);
lean_ctor_set(x_418, 0, x_422);
return x_418;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_418, 1);
lean_inc(x_423);
lean_dec(x_418);
x_424 = lean_box(0);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_426 = lean_ctor_get(x_418, 1);
lean_inc(x_426);
lean_dec(x_418);
x_427 = lean_ctor_get(x_419, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_419, 1);
lean_inc(x_428);
lean_dec(x_419);
x_429 = lean_nat_add(x_3, x_428);
lean_dec(x_428);
x_430 = lean_ctor_get(x_4, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_4, 2);
lean_inc(x_431);
lean_dec(x_4);
x_432 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_432, 0, x_427);
lean_ctor_set(x_432, 1, x_430);
lean_ctor_set(x_432, 2, x_431);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_5);
x_434 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_429, x_433, x_7, x_426);
lean_dec(x_7);
lean_dec(x_429);
return x_434;
}
}
else
{
uint8_t x_435; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_435 = !lean_is_exclusive(x_418);
if (x_435 == 0)
{
return x_418;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_418, 0);
x_437 = lean_ctor_get(x_418, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_418);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
}
}
}
}
case 3:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_439; uint8_t x_440; lean_object* x_441; 
lean_dec(x_21);
x_439 = lean_ctor_get(x_4, 2);
lean_inc(x_439);
x_440 = 1;
x_441 = l_Lean_Meta_substCore(x_1, x_2, x_440, x_439, x_7, x_31);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
lean_dec(x_441);
x_444 = lean_ctor_get(x_442, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_442, 1);
lean_inc(x_445);
lean_dec(x_442);
x_446 = lean_ctor_get(x_4, 1);
lean_inc(x_446);
lean_dec(x_4);
x_447 = x_446;
x_448 = lean_unsigned_to_nat(0u);
x_449 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__16(x_444, x_448, x_447);
x_450 = x_449;
x_451 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_451, 0, x_445);
lean_ctor_set(x_451, 1, x_450);
lean_ctor_set(x_451, 2, x_444);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_5);
x_453 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_452, x_7, x_443);
lean_dec(x_7);
return x_453;
}
else
{
uint8_t x_454; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_454 = !lean_is_exclusive(x_441);
if (x_454 == 0)
{
return x_441;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_441, 0);
x_456 = lean_ctor_get(x_441, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_441);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
lean_object* x_458; 
lean_dec(x_21);
x_458 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 0)
{
uint8_t x_460; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_460 = !lean_is_exclusive(x_458);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_458, 0);
lean_dec(x_461);
x_462 = lean_box(0);
lean_ctor_set(x_458, 0, x_462);
return x_458;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_458, 1);
lean_inc(x_463);
lean_dec(x_458);
x_464 = lean_box(0);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_466 = lean_ctor_get(x_458, 1);
lean_inc(x_466);
lean_dec(x_458);
x_467 = lean_ctor_get(x_459, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_459, 1);
lean_inc(x_468);
lean_dec(x_459);
x_469 = lean_nat_add(x_3, x_468);
lean_dec(x_468);
x_470 = lean_ctor_get(x_4, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_4, 2);
lean_inc(x_471);
lean_dec(x_4);
x_472 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_472, 0, x_467);
lean_ctor_set(x_472, 1, x_470);
lean_ctor_set(x_472, 2, x_471);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_5);
x_474 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_469, x_473, x_7, x_466);
lean_dec(x_7);
lean_dec(x_469);
return x_474;
}
}
else
{
uint8_t x_475; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_475 = !lean_is_exclusive(x_458);
if (x_475 == 0)
{
return x_458;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_458, 0);
x_477 = lean_ctor_get(x_458, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_458);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
}
case 4:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_479; uint8_t x_480; lean_object* x_481; 
lean_dec(x_21);
x_479 = lean_ctor_get(x_4, 2);
lean_inc(x_479);
x_480 = 1;
x_481 = l_Lean_Meta_substCore(x_1, x_2, x_480, x_479, x_7, x_31);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_ctor_get(x_482, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_485);
lean_dec(x_482);
x_486 = lean_ctor_get(x_4, 1);
lean_inc(x_486);
lean_dec(x_4);
x_487 = x_486;
x_488 = lean_unsigned_to_nat(0u);
x_489 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__17(x_484, x_488, x_487);
x_490 = x_489;
x_491 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_491, 0, x_485);
lean_ctor_set(x_491, 1, x_490);
lean_ctor_set(x_491, 2, x_484);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_5);
x_493 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_492, x_7, x_483);
lean_dec(x_7);
return x_493;
}
else
{
uint8_t x_494; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_494 = !lean_is_exclusive(x_481);
if (x_494 == 0)
{
return x_481;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_481, 0);
x_496 = lean_ctor_get(x_481, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_481);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
}
}
else
{
lean_object* x_498; 
lean_dec(x_21);
x_498 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
if (lean_obj_tag(x_499) == 0)
{
uint8_t x_500; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_500 = !lean_is_exclusive(x_498);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; 
x_501 = lean_ctor_get(x_498, 0);
lean_dec(x_501);
x_502 = lean_box(0);
lean_ctor_set(x_498, 0, x_502);
return x_498;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_498, 1);
lean_inc(x_503);
lean_dec(x_498);
x_504 = lean_box(0);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_506 = lean_ctor_get(x_498, 1);
lean_inc(x_506);
lean_dec(x_498);
x_507 = lean_ctor_get(x_499, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_499, 1);
lean_inc(x_508);
lean_dec(x_499);
x_509 = lean_nat_add(x_3, x_508);
lean_dec(x_508);
x_510 = lean_ctor_get(x_4, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_4, 2);
lean_inc(x_511);
lean_dec(x_4);
x_512 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_512, 0, x_507);
lean_ctor_set(x_512, 1, x_510);
lean_ctor_set(x_512, 2, x_511);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_5);
x_514 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_509, x_513, x_7, x_506);
lean_dec(x_7);
lean_dec(x_509);
return x_514;
}
}
else
{
uint8_t x_515; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_515 = !lean_is_exclusive(x_498);
if (x_515 == 0)
{
return x_498;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_498, 0);
x_517 = lean_ctor_get(x_498, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_498);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
return x_518;
}
}
}
}
case 5:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_519; uint8_t x_520; lean_object* x_521; 
lean_dec(x_21);
x_519 = lean_ctor_get(x_4, 2);
lean_inc(x_519);
x_520 = 1;
x_521 = l_Lean_Meta_substCore(x_1, x_2, x_520, x_519, x_7, x_31);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_dec(x_522);
x_526 = lean_ctor_get(x_4, 1);
lean_inc(x_526);
lean_dec(x_4);
x_527 = x_526;
x_528 = lean_unsigned_to_nat(0u);
x_529 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__18(x_524, x_528, x_527);
x_530 = x_529;
x_531 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_531, 0, x_525);
lean_ctor_set(x_531, 1, x_530);
lean_ctor_set(x_531, 2, x_524);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_5);
x_533 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_532, x_7, x_523);
lean_dec(x_7);
return x_533;
}
else
{
uint8_t x_534; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_534 = !lean_is_exclusive(x_521);
if (x_534 == 0)
{
return x_521;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_521, 0);
x_536 = lean_ctor_get(x_521, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_521);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
else
{
lean_object* x_538; 
lean_dec(x_21);
x_538 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
if (lean_obj_tag(x_539) == 0)
{
uint8_t x_540; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_540 = !lean_is_exclusive(x_538);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_ctor_get(x_538, 0);
lean_dec(x_541);
x_542 = lean_box(0);
lean_ctor_set(x_538, 0, x_542);
return x_538;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_538, 1);
lean_inc(x_543);
lean_dec(x_538);
x_544 = lean_box(0);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_546 = lean_ctor_get(x_538, 1);
lean_inc(x_546);
lean_dec(x_538);
x_547 = lean_ctor_get(x_539, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_539, 1);
lean_inc(x_548);
lean_dec(x_539);
x_549 = lean_nat_add(x_3, x_548);
lean_dec(x_548);
x_550 = lean_ctor_get(x_4, 1);
lean_inc(x_550);
x_551 = lean_ctor_get(x_4, 2);
lean_inc(x_551);
lean_dec(x_4);
x_552 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_552, 0, x_547);
lean_ctor_set(x_552, 1, x_550);
lean_ctor_set(x_552, 2, x_551);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_5);
x_554 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_549, x_553, x_7, x_546);
lean_dec(x_7);
lean_dec(x_549);
return x_554;
}
}
else
{
uint8_t x_555; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_555 = !lean_is_exclusive(x_538);
if (x_555 == 0)
{
return x_538;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_538, 0);
x_557 = lean_ctor_get(x_538, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_538);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_557);
return x_558;
}
}
}
}
case 6:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_559; uint8_t x_560; lean_object* x_561; 
lean_dec(x_21);
x_559 = lean_ctor_get(x_4, 2);
lean_inc(x_559);
x_560 = 1;
x_561 = l_Lean_Meta_substCore(x_1, x_2, x_560, x_559, x_7, x_31);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = lean_ctor_get(x_562, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_562, 1);
lean_inc(x_565);
lean_dec(x_562);
x_566 = lean_ctor_get(x_4, 1);
lean_inc(x_566);
lean_dec(x_4);
x_567 = x_566;
x_568 = lean_unsigned_to_nat(0u);
x_569 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__19(x_564, x_568, x_567);
x_570 = x_569;
x_571 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_571, 0, x_565);
lean_ctor_set(x_571, 1, x_570);
lean_ctor_set(x_571, 2, x_564);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_5);
x_573 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_572, x_7, x_563);
lean_dec(x_7);
return x_573;
}
else
{
uint8_t x_574; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_574 = !lean_is_exclusive(x_561);
if (x_574 == 0)
{
return x_561;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_561, 0);
x_576 = lean_ctor_get(x_561, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_561);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set(x_577, 1, x_576);
return x_577;
}
}
}
else
{
lean_object* x_578; 
lean_dec(x_21);
x_578 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
if (lean_obj_tag(x_579) == 0)
{
uint8_t x_580; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_580 = !lean_is_exclusive(x_578);
if (x_580 == 0)
{
lean_object* x_581; lean_object* x_582; 
x_581 = lean_ctor_get(x_578, 0);
lean_dec(x_581);
x_582 = lean_box(0);
lean_ctor_set(x_578, 0, x_582);
return x_578;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_578, 1);
lean_inc(x_583);
lean_dec(x_578);
x_584 = lean_box(0);
x_585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_585, 0, x_584);
lean_ctor_set(x_585, 1, x_583);
return x_585;
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_586 = lean_ctor_get(x_578, 1);
lean_inc(x_586);
lean_dec(x_578);
x_587 = lean_ctor_get(x_579, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_579, 1);
lean_inc(x_588);
lean_dec(x_579);
x_589 = lean_nat_add(x_3, x_588);
lean_dec(x_588);
x_590 = lean_ctor_get(x_4, 1);
lean_inc(x_590);
x_591 = lean_ctor_get(x_4, 2);
lean_inc(x_591);
lean_dec(x_4);
x_592 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_592, 0, x_587);
lean_ctor_set(x_592, 1, x_590);
lean_ctor_set(x_592, 2, x_591);
x_593 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_5);
x_594 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_589, x_593, x_7, x_586);
lean_dec(x_7);
lean_dec(x_589);
return x_594;
}
}
else
{
uint8_t x_595; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_595 = !lean_is_exclusive(x_578);
if (x_595 == 0)
{
return x_578;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_578, 0);
x_597 = lean_ctor_get(x_578, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_578);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
}
case 7:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_599; uint8_t x_600; lean_object* x_601; 
lean_dec(x_21);
x_599 = lean_ctor_get(x_4, 2);
lean_inc(x_599);
x_600 = 1;
x_601 = l_Lean_Meta_substCore(x_1, x_2, x_600, x_599, x_7, x_31);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_ctor_get(x_602, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_602, 1);
lean_inc(x_605);
lean_dec(x_602);
x_606 = lean_ctor_get(x_4, 1);
lean_inc(x_606);
lean_dec(x_4);
x_607 = x_606;
x_608 = lean_unsigned_to_nat(0u);
x_609 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__20(x_604, x_608, x_607);
x_610 = x_609;
x_611 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_611, 0, x_605);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set(x_611, 2, x_604);
x_612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_5);
x_613 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_612, x_7, x_603);
lean_dec(x_7);
return x_613;
}
else
{
uint8_t x_614; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_614 = !lean_is_exclusive(x_601);
if (x_614 == 0)
{
return x_601;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_601, 0);
x_616 = lean_ctor_get(x_601, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_601);
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
lean_dec(x_21);
x_618 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
if (lean_obj_tag(x_619) == 0)
{
uint8_t x_620; 
lean_dec(x_7);
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
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
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
x_630 = lean_ctor_get(x_4, 1);
lean_inc(x_630);
x_631 = lean_ctor_get(x_4, 2);
lean_inc(x_631);
lean_dec(x_4);
x_632 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_632, 0, x_627);
lean_ctor_set(x_632, 1, x_630);
lean_ctor_set(x_632, 2, x_631);
x_633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_5);
x_634 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_629, x_633, x_7, x_626);
lean_dec(x_7);
lean_dec(x_629);
return x_634;
}
}
else
{
uint8_t x_635; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_635 = !lean_is_exclusive(x_618);
if (x_635 == 0)
{
return x_618;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_618, 0);
x_637 = lean_ctor_get(x_618, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_618);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
}
case 8:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_639; uint8_t x_640; lean_object* x_641; 
lean_dec(x_21);
x_639 = lean_ctor_get(x_4, 2);
lean_inc(x_639);
x_640 = 1;
x_641 = l_Lean_Meta_substCore(x_1, x_2, x_640, x_639, x_7, x_31);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
x_644 = lean_ctor_get(x_642, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_642, 1);
lean_inc(x_645);
lean_dec(x_642);
x_646 = lean_ctor_get(x_4, 1);
lean_inc(x_646);
lean_dec(x_4);
x_647 = x_646;
x_648 = lean_unsigned_to_nat(0u);
x_649 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__21(x_644, x_648, x_647);
x_650 = x_649;
x_651 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_651, 0, x_645);
lean_ctor_set(x_651, 1, x_650);
lean_ctor_set(x_651, 2, x_644);
x_652 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_5);
x_653 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_652, x_7, x_643);
lean_dec(x_7);
return x_653;
}
else
{
uint8_t x_654; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_654 = !lean_is_exclusive(x_641);
if (x_654 == 0)
{
return x_641;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_641, 0);
x_656 = lean_ctor_get(x_641, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_641);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
}
else
{
lean_object* x_658; 
lean_dec(x_21);
x_658 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
if (lean_obj_tag(x_659) == 0)
{
uint8_t x_660; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_660 = !lean_is_exclusive(x_658);
if (x_660 == 0)
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_ctor_get(x_658, 0);
lean_dec(x_661);
x_662 = lean_box(0);
lean_ctor_set(x_658, 0, x_662);
return x_658;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_658, 1);
lean_inc(x_663);
lean_dec(x_658);
x_664 = lean_box(0);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_663);
return x_665;
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_666 = lean_ctor_get(x_658, 1);
lean_inc(x_666);
lean_dec(x_658);
x_667 = lean_ctor_get(x_659, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_659, 1);
lean_inc(x_668);
lean_dec(x_659);
x_669 = lean_nat_add(x_3, x_668);
lean_dec(x_668);
x_670 = lean_ctor_get(x_4, 1);
lean_inc(x_670);
x_671 = lean_ctor_get(x_4, 2);
lean_inc(x_671);
lean_dec(x_4);
x_672 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_672, 0, x_667);
lean_ctor_set(x_672, 1, x_670);
lean_ctor_set(x_672, 2, x_671);
x_673 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_5);
x_674 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_669, x_673, x_7, x_666);
lean_dec(x_7);
lean_dec(x_669);
return x_674;
}
}
else
{
uint8_t x_675; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_675 = !lean_is_exclusive(x_658);
if (x_675 == 0)
{
return x_658;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_658, 0);
x_677 = lean_ctor_get(x_658, 1);
lean_inc(x_677);
lean_inc(x_676);
lean_dec(x_658);
x_678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
return x_678;
}
}
}
}
case 9:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_679; uint8_t x_680; lean_object* x_681; 
lean_dec(x_21);
x_679 = lean_ctor_get(x_4, 2);
lean_inc(x_679);
x_680 = 1;
x_681 = l_Lean_Meta_substCore(x_1, x_2, x_680, x_679, x_7, x_31);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_684 = lean_ctor_get(x_682, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
lean_dec(x_682);
x_686 = lean_ctor_get(x_4, 1);
lean_inc(x_686);
lean_dec(x_4);
x_687 = x_686;
x_688 = lean_unsigned_to_nat(0u);
x_689 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__22(x_684, x_688, x_687);
x_690 = x_689;
x_691 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_691, 0, x_685);
lean_ctor_set(x_691, 1, x_690);
lean_ctor_set(x_691, 2, x_684);
x_692 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_5);
x_693 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_692, x_7, x_683);
lean_dec(x_7);
return x_693;
}
else
{
uint8_t x_694; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_694 = !lean_is_exclusive(x_681);
if (x_694 == 0)
{
return x_681;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_681, 0);
x_696 = lean_ctor_get(x_681, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_681);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
return x_697;
}
}
}
else
{
lean_object* x_698; 
lean_dec(x_21);
x_698 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_698) == 0)
{
lean_object* x_699; 
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
if (lean_obj_tag(x_699) == 0)
{
uint8_t x_700; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_700 = !lean_is_exclusive(x_698);
if (x_700 == 0)
{
lean_object* x_701; lean_object* x_702; 
x_701 = lean_ctor_get(x_698, 0);
lean_dec(x_701);
x_702 = lean_box(0);
lean_ctor_set(x_698, 0, x_702);
return x_698;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_703 = lean_ctor_get(x_698, 1);
lean_inc(x_703);
lean_dec(x_698);
x_704 = lean_box(0);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_703);
return x_705;
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_706 = lean_ctor_get(x_698, 1);
lean_inc(x_706);
lean_dec(x_698);
x_707 = lean_ctor_get(x_699, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_699, 1);
lean_inc(x_708);
lean_dec(x_699);
x_709 = lean_nat_add(x_3, x_708);
lean_dec(x_708);
x_710 = lean_ctor_get(x_4, 1);
lean_inc(x_710);
x_711 = lean_ctor_get(x_4, 2);
lean_inc(x_711);
lean_dec(x_4);
x_712 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_712, 0, x_707);
lean_ctor_set(x_712, 1, x_710);
lean_ctor_set(x_712, 2, x_711);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_5);
x_714 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_709, x_713, x_7, x_706);
lean_dec(x_7);
lean_dec(x_709);
return x_714;
}
}
else
{
uint8_t x_715; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_715 = !lean_is_exclusive(x_698);
if (x_715 == 0)
{
return x_698;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_698, 0);
x_717 = lean_ctor_get(x_698, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_698);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
}
}
case 10:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_719; uint8_t x_720; lean_object* x_721; 
lean_dec(x_21);
x_719 = lean_ctor_get(x_4, 2);
lean_inc(x_719);
x_720 = 1;
x_721 = l_Lean_Meta_substCore(x_1, x_2, x_720, x_719, x_7, x_31);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_724 = lean_ctor_get(x_722, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_722, 1);
lean_inc(x_725);
lean_dec(x_722);
x_726 = lean_ctor_get(x_4, 1);
lean_inc(x_726);
lean_dec(x_4);
x_727 = x_726;
x_728 = lean_unsigned_to_nat(0u);
x_729 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__23(x_724, x_728, x_727);
x_730 = x_729;
x_731 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_731, 0, x_725);
lean_ctor_set(x_731, 1, x_730);
lean_ctor_set(x_731, 2, x_724);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_5);
x_733 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_732, x_7, x_723);
lean_dec(x_7);
return x_733;
}
else
{
uint8_t x_734; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_734 = !lean_is_exclusive(x_721);
if (x_734 == 0)
{
return x_721;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_721, 0);
x_736 = lean_ctor_get(x_721, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_721);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
}
}
else
{
lean_object* x_738; 
lean_dec(x_21);
x_738 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
if (lean_obj_tag(x_739) == 0)
{
uint8_t x_740; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_740 = !lean_is_exclusive(x_738);
if (x_740 == 0)
{
lean_object* x_741; lean_object* x_742; 
x_741 = lean_ctor_get(x_738, 0);
lean_dec(x_741);
x_742 = lean_box(0);
lean_ctor_set(x_738, 0, x_742);
return x_738;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_738, 1);
lean_inc(x_743);
lean_dec(x_738);
x_744 = lean_box(0);
x_745 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_746 = lean_ctor_get(x_738, 1);
lean_inc(x_746);
lean_dec(x_738);
x_747 = lean_ctor_get(x_739, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_739, 1);
lean_inc(x_748);
lean_dec(x_739);
x_749 = lean_nat_add(x_3, x_748);
lean_dec(x_748);
x_750 = lean_ctor_get(x_4, 1);
lean_inc(x_750);
x_751 = lean_ctor_get(x_4, 2);
lean_inc(x_751);
lean_dec(x_4);
x_752 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_752, 0, x_747);
lean_ctor_set(x_752, 1, x_750);
lean_ctor_set(x_752, 2, x_751);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_5);
x_754 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_749, x_753, x_7, x_746);
lean_dec(x_7);
lean_dec(x_749);
return x_754;
}
}
else
{
uint8_t x_755; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_755 = !lean_is_exclusive(x_738);
if (x_755 == 0)
{
return x_738;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_738, 0);
x_757 = lean_ctor_get(x_738, 1);
lean_inc(x_757);
lean_inc(x_756);
lean_dec(x_738);
x_758 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_758, 0, x_756);
lean_ctor_set(x_758, 1, x_757);
return x_758;
}
}
}
}
case 11:
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_759; uint8_t x_760; lean_object* x_761; 
lean_dec(x_21);
x_759 = lean_ctor_get(x_4, 2);
lean_inc(x_759);
x_760 = 1;
x_761 = l_Lean_Meta_substCore(x_1, x_2, x_760, x_759, x_7, x_31);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
x_764 = lean_ctor_get(x_762, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_762, 1);
lean_inc(x_765);
lean_dec(x_762);
x_766 = lean_ctor_get(x_4, 1);
lean_inc(x_766);
lean_dec(x_4);
x_767 = x_766;
x_768 = lean_unsigned_to_nat(0u);
x_769 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__24(x_764, x_768, x_767);
x_770 = x_769;
x_771 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_771, 0, x_765);
lean_ctor_set(x_771, 1, x_770);
lean_ctor_set(x_771, 2, x_764);
x_772 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_772, 0, x_771);
lean_ctor_set(x_772, 1, x_5);
x_773 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_772, x_7, x_763);
lean_dec(x_7);
return x_773;
}
else
{
uint8_t x_774; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_774 = !lean_is_exclusive(x_761);
if (x_774 == 0)
{
return x_761;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_775 = lean_ctor_get(x_761, 0);
x_776 = lean_ctor_get(x_761, 1);
lean_inc(x_776);
lean_inc(x_775);
lean_dec(x_761);
x_777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_777, 0, x_775);
lean_ctor_set(x_777, 1, x_776);
return x_777;
}
}
}
else
{
lean_object* x_778; 
lean_dec(x_21);
x_778 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; 
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
if (lean_obj_tag(x_779) == 0)
{
uint8_t x_780; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_780 = !lean_is_exclusive(x_778);
if (x_780 == 0)
{
lean_object* x_781; lean_object* x_782; 
x_781 = lean_ctor_get(x_778, 0);
lean_dec(x_781);
x_782 = lean_box(0);
lean_ctor_set(x_778, 0, x_782);
return x_778;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_783 = lean_ctor_get(x_778, 1);
lean_inc(x_783);
lean_dec(x_778);
x_784 = lean_box(0);
x_785 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_783);
return x_785;
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_786 = lean_ctor_get(x_778, 1);
lean_inc(x_786);
lean_dec(x_778);
x_787 = lean_ctor_get(x_779, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_779, 1);
lean_inc(x_788);
lean_dec(x_779);
x_789 = lean_nat_add(x_3, x_788);
lean_dec(x_788);
x_790 = lean_ctor_get(x_4, 1);
lean_inc(x_790);
x_791 = lean_ctor_get(x_4, 2);
lean_inc(x_791);
lean_dec(x_4);
x_792 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_792, 0, x_787);
lean_ctor_set(x_792, 1, x_790);
lean_ctor_set(x_792, 2, x_791);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_5);
x_794 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_789, x_793, x_7, x_786);
lean_dec(x_7);
lean_dec(x_789);
return x_794;
}
}
else
{
uint8_t x_795; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_795 = !lean_is_exclusive(x_778);
if (x_795 == 0)
{
return x_778;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_796 = lean_ctor_get(x_778, 0);
x_797 = lean_ctor_get(x_778, 1);
lean_inc(x_797);
lean_inc(x_796);
lean_dec(x_778);
x_798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_798, 0, x_796);
lean_ctor_set(x_798, 1, x_797);
return x_798;
}
}
}
}
default: 
{
lean_dec(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_799; uint8_t x_800; lean_object* x_801; 
lean_dec(x_21);
x_799 = lean_ctor_get(x_4, 2);
lean_inc(x_799);
x_800 = 1;
x_801 = l_Lean_Meta_substCore(x_1, x_2, x_800, x_799, x_7, x_31);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
lean_dec(x_801);
x_804 = lean_ctor_get(x_802, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_802, 1);
lean_inc(x_805);
lean_dec(x_802);
x_806 = lean_ctor_get(x_4, 1);
lean_inc(x_806);
lean_dec(x_4);
x_807 = x_806;
x_808 = lean_unsigned_to_nat(0u);
x_809 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__25(x_804, x_808, x_807);
x_810 = x_809;
x_811 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_811, 0, x_805);
lean_ctor_set(x_811, 1, x_810);
lean_ctor_set(x_811, 2, x_804);
x_812 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_5);
x_813 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_812, x_7, x_803);
lean_dec(x_7);
return x_813;
}
else
{
uint8_t x_814; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_814 = !lean_is_exclusive(x_801);
if (x_814 == 0)
{
return x_801;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_801, 0);
x_816 = lean_ctor_get(x_801, 1);
lean_inc(x_816);
lean_inc(x_815);
lean_dec(x_801);
x_817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
return x_817;
}
}
}
else
{
lean_object* x_818; 
lean_dec(x_21);
x_818 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_31);
if (lean_obj_tag(x_818) == 0)
{
lean_object* x_819; 
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
if (lean_obj_tag(x_819) == 0)
{
uint8_t x_820; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_820 = !lean_is_exclusive(x_818);
if (x_820 == 0)
{
lean_object* x_821; lean_object* x_822; 
x_821 = lean_ctor_get(x_818, 0);
lean_dec(x_821);
x_822 = lean_box(0);
lean_ctor_set(x_818, 0, x_822);
return x_818;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = lean_ctor_get(x_818, 1);
lean_inc(x_823);
lean_dec(x_818);
x_824 = lean_box(0);
x_825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
return x_825;
}
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_826 = lean_ctor_get(x_818, 1);
lean_inc(x_826);
lean_dec(x_818);
x_827 = lean_ctor_get(x_819, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_819, 1);
lean_inc(x_828);
lean_dec(x_819);
x_829 = lean_nat_add(x_3, x_828);
lean_dec(x_828);
x_830 = lean_ctor_get(x_4, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_4, 2);
lean_inc(x_831);
lean_dec(x_4);
x_832 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_832, 0, x_827);
lean_ctor_set(x_832, 1, x_830);
lean_ctor_set(x_832, 2, x_831);
x_833 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_5);
x_834 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_829, x_833, x_7, x_826);
lean_dec(x_7);
lean_dec(x_829);
return x_834;
}
}
else
{
uint8_t x_835; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_835 = !lean_is_exclusive(x_818);
if (x_835 == 0)
{
return x_818;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_836 = lean_ctor_get(x_818, 0);
x_837 = lean_ctor_get(x_818, 1);
lean_inc(x_837);
lean_inc(x_836);
lean_dec(x_818);
x_838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_838, 0, x_836);
lean_ctor_set(x_838, 1, x_837);
return x_838;
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
uint8_t x_839; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_839 = !lean_is_exclusive(x_29);
if (x_839 == 0)
{
return x_29;
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_840 = lean_ctor_get(x_29, 0);
x_841 = lean_ctor_get(x_29, 1);
lean_inc(x_841);
lean_inc(x_840);
lean_dec(x_29);
x_842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_842, 0, x_840);
lean_ctor_set(x_842, 1, x_841);
return x_842;
}
}
}
else
{
uint8_t x_843; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_843 = !lean_is_exclusive(x_26);
if (x_843 == 0)
{
return x_26;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_844 = lean_ctor_get(x_26, 0);
x_845 = lean_ctor_get(x_26, 1);
lean_inc(x_845);
lean_inc(x_844);
lean_dec(x_26);
x_846 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_846, 0, x_844);
lean_ctor_set(x_846, 1, x_845);
return x_846;
}
}
}
else
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
x_847 = lean_ctor_get(x_22, 1);
lean_inc(x_847);
lean_dec(x_22);
x_848 = l_Lean_Meta_clear(x_1, x_2, x_7, x_847);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
lean_dec(x_848);
x_851 = lean_ctor_get(x_4, 1);
lean_inc(x_851);
x_852 = lean_ctor_get(x_4, 2);
lean_inc(x_852);
lean_dec(x_4);
x_853 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_853, 0, x_849);
lean_ctor_set(x_853, 1, x_851);
lean_ctor_set(x_853, 2, x_852);
x_854 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_5);
x_855 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_3, x_854, x_7, x_850);
lean_dec(x_7);
return x_855;
}
else
{
uint8_t x_856; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_856 = !lean_is_exclusive(x_848);
if (x_856 == 0)
{
return x_848;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_857 = lean_ctor_get(x_848, 0);
x_858 = lean_ctor_get(x_848, 1);
lean_inc(x_858);
lean_inc(x_857);
lean_dec(x_848);
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_857);
lean_ctor_set(x_859, 1, x_858);
return x_859;
}
}
}
}
else
{
uint8_t x_860; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_860 = !lean_is_exclusive(x_22);
if (x_860 == 0)
{
return x_22;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_22, 0);
x_862 = lean_ctor_get(x_22, 1);
lean_inc(x_862);
lean_inc(x_861);
lean_dec(x_22);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_862);
return x_863;
}
}
}
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_864 = l_Lean_Expr_appFn_x21(x_9);
x_865 = l_Lean_Expr_appFn_x21(x_864);
lean_dec(x_864);
x_866 = l_Lean_Expr_appArg_x21(x_865);
lean_dec(x_865);
x_867 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_2);
x_868 = l_Lean_mkFVar(x_2);
lean_inc(x_7);
x_869 = l_Lean_Meta_mkEqOfHEq(x_868, x_7, x_8);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
lean_inc(x_7);
x_872 = l_Lean_Meta_mkEq(x_866, x_867, x_7, x_871);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = l_Lean_LocalDecl_userName(x_6);
x_876 = l_Lean_Meta_assert(x_1, x_875, x_873, x_870, x_7, x_874);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec(x_876);
x_879 = l_Lean_Meta_clear(x_877, x_2, x_7, x_878);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_879, 1);
lean_inc(x_881);
lean_dec(x_879);
x_882 = lean_unsigned_to_nat(1u);
x_883 = lean_nat_add(x_3, x_882);
x_884 = lean_ctor_get(x_4, 1);
lean_inc(x_884);
x_885 = lean_ctor_get(x_4, 2);
lean_inc(x_885);
lean_dec(x_4);
x_886 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_886, 0, x_880);
lean_ctor_set(x_886, 1, x_884);
lean_ctor_set(x_886, 2, x_885);
x_887 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_887, 0, x_886);
lean_ctor_set(x_887, 1, x_5);
x_888 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_883, x_887, x_7, x_881);
lean_dec(x_7);
lean_dec(x_883);
return x_888;
}
else
{
uint8_t x_889; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_889 = !lean_is_exclusive(x_879);
if (x_889 == 0)
{
return x_879;
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_890 = lean_ctor_get(x_879, 0);
x_891 = lean_ctor_get(x_879, 1);
lean_inc(x_891);
lean_inc(x_890);
lean_dec(x_879);
x_892 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_892, 0, x_890);
lean_ctor_set(x_892, 1, x_891);
return x_892;
}
}
}
else
{
uint8_t x_893; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_893 = !lean_is_exclusive(x_876);
if (x_893 == 0)
{
return x_876;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_876, 0);
x_895 = lean_ctor_get(x_876, 1);
lean_inc(x_895);
lean_inc(x_894);
lean_dec(x_876);
x_896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set(x_896, 1, x_895);
return x_896;
}
}
}
else
{
uint8_t x_897; 
lean_dec(x_870);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_897 = !lean_is_exclusive(x_872);
if (x_897 == 0)
{
return x_872;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_872, 0);
x_899 = lean_ctor_get(x_872, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_872);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
}
else
{
uint8_t x_901; 
lean_dec(x_867);
lean_dec(x_866);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_901 = !lean_is_exclusive(x_869);
if (x_901 == 0)
{
return x_869;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_902 = lean_ctor_get(x_869, 0);
x_903 = lean_ctor_get(x_869, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_869);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs [");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_37; uint8_t x_38; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_37 = lean_ctor_get(x_4, 4);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
if (x_38 == 0)
{
x_12 = x_4;
goto block_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_40 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_39, x_3, x_4);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_12 = x_43;
goto block_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_nat_add(x_8, x_7);
x_46 = l_Nat_repr(x_45);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_11);
x_53 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_53, 0, x_11);
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_39, x_54, x_3, x_44);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_12 = x_56;
goto block_36;
}
}
block_36:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = l_Lean_Meta_intro1(x_11, x_13, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_19, 0, x_17);
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___boxed), 8, 5);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_8);
lean_closure_set(x_20, 3, x_9);
lean_closure_set(x_20, 4, x_10);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_getMVarDecl(x_18, x_3, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 4);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_withLocalContext___rarg(x_25, x_26, x_21, x_3, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
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
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_inc(x_2);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_2);
x_58 = lean_ctor_get(x_4, 4);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_58, sizeof(void*)*1);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_62 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_61, x_3, x_4);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_62, 0);
lean_dec(x_66);
lean_ctor_set(x_62, 0, x_57);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
lean_dec(x_2);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_61, x_74, x_3, x_70);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_57);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_57);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__10(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__11(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__12(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__13(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__14(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__15(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__16(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__17(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__18(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__19(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__20(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__21(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__22(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__23(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__24(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___spec__25(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main(x_1, x_11, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_4 = x_13;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_array_push(x_5, x_19);
x_4 = x_13;
x_5 = x_20;
x_7 = x_18;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_5);
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
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not applicable to the given hypothesis");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after generalizeIndices");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__6;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_3);
x_10 = l___private_Lean_Meta_Tactic_Cases_4__mkCasesContext_x3f(x_3, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Cases_cases___lambda__1___closed__3;
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_13, x_6, x_12);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
x_19 = l_List_redLength___main___rarg(x_18);
x_20 = lean_mk_empty_array_with_capacity(x_19);
lean_dec(x_19);
x_21 = l_List_toArrayAux___main___rarg(x_18, x_20);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_casesOnSuffix;
x_25 = lean_name_mk_string(x_23, x_24);
x_26 = l___private_Lean_Meta_Tactic_Cases_5__hasIndepIndices(x_16, x_6, x_15);
lean_dec(x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_78; uint8_t x_79; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
x_78 = lean_ctor_get(x_32, 4);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
lean_dec(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = 0;
x_35 = x_80;
x_36 = x_32;
goto block_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_82 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_81, x_6, x_32);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_35 = x_85;
x_36 = x_84;
goto block_77;
}
block_77:
{
if (x_35 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Meta_induction(x_33, x_34, x_25, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_6);
lean_inc(x_31);
x_40 = l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(x_31, x_38, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_41, x_21);
lean_dec(x_21);
x_44 = lean_ctor_get(x_31, 3);
lean_inc(x_44);
lean_dec(x_31);
x_45 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(x_44, x_43, x_6, x_42);
lean_dec(x_6);
lean_dec(x_43);
lean_dec(x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
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
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_33);
x_54 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_54, 0, x_33);
x_55 = l_Lean_Meta_Cases_cases___lambda__1___closed__7;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
x_58 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_57, x_56, x_6, x_36);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Meta_induction(x_33, x_34, x_25, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_6);
lean_inc(x_31);
x_63 = l___private_Lean_Meta_Tactic_Cases_6__elimAuxIndices(x_31, x_61, x_6, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_64, x_21);
lean_dec(x_21);
x_67 = lean_ctor_get(x_31, 3);
lean_inc(x_67);
lean_dec(x_31);
x_68 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqs(x_67, x_66, x_6, x_65);
lean_dec(x_6);
lean_dec(x_66);
lean_dec(x_67);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
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
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_6);
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
}
}
else
{
uint8_t x_86; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_30);
if (x_86 == 0)
{
return x_30;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_30, 0);
x_88 = lean_ctor_get(x_30, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_30);
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
x_90 = lean_ctor_get(x_26, 1);
lean_inc(x_90);
lean_dec(x_26);
x_91 = l_Lean_Meta_induction(x_1, x_3, x_25, x_4, x_5, x_6, x_90);
lean_dec(x_6);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_93, x_21);
lean_dec(x_21);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_91);
x_97 = l___private_Lean_Meta_Tactic_Cases_7__toCasesSubgoals(x_95, x_21);
lean_dec(x_21);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_21);
x_99 = !lean_is_exclusive(x_91);
if (x_99 == 0)
{
return x_91;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_91, 0);
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_91);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_10);
if (x_103 == 0)
{
return x_10;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_10, 0);
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_10);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_8);
if (x_107 == 0)
{
return x_8;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_8, 0);
x_109 = lean_ctor_get(x_8, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_8);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2;
x_8 = lean_box(x_4);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__1___boxed), 7, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_8);
x_10 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 4);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_withLocalContext___rarg(x_13, x_14, x_9, x_5, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
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
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Meta_Cases_cases___lambda__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Cases_cases(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_cases(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_10__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1;
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
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__1);
l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_2__withNewIndexEqsAux___main___rarg___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6);
l_Lean_Meta_generalizeIndices___lambda__1___closed__1 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__1);
l_Lean_Meta_generalizeIndices___lambda__1___closed__2 = _init_l_Lean_Meta_generalizeIndices___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___lambda__1___closed__2);
l_Lean_Meta_generalizeIndices___closed__1 = _init_l_Lean_Meta_generalizeIndices___closed__1();
lean_mark_persistent(l_Lean_Meta_generalizeIndices___closed__1);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__1);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__2);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__3);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__4);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__5);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__6);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__7);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__8);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__9);
l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10 = _init_l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_8__unifyEqsAux___main___closed__10);
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
l_Lean_Meta_Cases_cases___lambda__1___closed__6 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__6);
l_Lean_Meta_Cases_cases___lambda__1___closed__7 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__7);
res = l___private_Lean_Meta_Tactic_Cases_10__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
