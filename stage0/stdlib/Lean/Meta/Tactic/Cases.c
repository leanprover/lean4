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
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__9;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__8;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__7;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__3;
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__2;
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__5;
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_6__visit_x3f(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwOther___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__7;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkNoConfusion___closed__8;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkHEqRefl___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___closed__1;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__2;
lean_object* l_List_redLength___main___rarg(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__1;
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
extern lean_object* l_Lean_Meta_mkEqRefl___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkNoConfusion___closed__5;
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__10;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__5;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3;
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_12__regTraceClasses(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compile pattern matching, inductive type expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = l_Lean_indentExpr(x_4);
x_6 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = l_Lean_Meta_throwOther___rarg(x_7, x_8, x_2, x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_Meta_whnfD(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_getAppFn___main(x_7);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_environment_find(x_4, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_free_object(x_5);
x_13 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_7, x_2, x_8);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_16);
x_18 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l___private_Lean_Expr_3__getAppArgsAux___main(x_7, x_19, x_21);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Array_extract___rarg(x_22, x_16, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_5, 0, x_25);
return x_5;
}
else
{
lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_11);
lean_free_object(x_5);
x_26 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_7, x_2, x_8);
lean_dec(x_2);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_free_object(x_5);
lean_dec(x_4);
x_27 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_7, x_2, x_8);
lean_dec(x_2);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_30 = l_Lean_Expr_getAppFn___main(x_28);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_environment_find(x_4, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_28, x_2, x_29);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 5)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_37);
x_39 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_38);
x_40 = lean_mk_array(x_38, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_38, x_41);
lean_dec(x_38);
x_43 = l___private_Lean_Expr_3__getAppArgsAux___main(x_28, x_40, x_42);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = l_Array_extract___rarg(x_43, x_37, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_29);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_35);
lean_dec(x_32);
x_48 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_28, x_2, x_29);
lean_dec(x_2);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_30);
lean_dec(x_4);
x_49 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_28, x_2, x_29);
lean_dec(x_2);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_5);
if (x_50 == 0)
{
return x_5;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_5, 0);
x_52 = lean_ctor_get(x_5, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_5);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = lean_array_push(x_2, x_8);
x_14 = lean_array_push(x_3, x_4);
x_15 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(x_5, x_6, x_7, x_12, x_13, x_14, x_9, x_10);
return x_15;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_15 = l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(x_13, x_14, x_7, x_8);
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
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_6);
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_1);
lean_closure_set(x_20, 5, x_2);
lean_closure_set(x_20, 6, x_3);
x_21 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_6, x_7, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg), 5, 0);
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
x_45 = l_Lean_Meta_introN(x_39, x_40, x_41, x_44, x_11, x_43);
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
x_13 = l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(x_12, x_2, x_10, x_11);
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
x_20 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2;
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
x_11 = l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg(x_6, x_3, x_10, x_8, x_9);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_mkNoConfusion___closed__8;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_14, x_15, x_10, x_11);
lean_dec(x_10);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
x_22 = lean_array_get_size(x_8);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_nat_add(x_19, x_23);
x_25 = lean_nat_dec_eq(x_22, x_24);
lean_dec(x_24);
x_26 = lean_nat_sub(x_22, x_19);
lean_dec(x_19);
x_27 = l_Array_extract___rarg(x_8, x_26, x_22);
lean_dec(x_22);
x_28 = l_Array_extract___rarg(x_8, x_20, x_23);
lean_dec(x_23);
lean_dec(x_8);
x_29 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_28, x_28, x_20, x_7);
lean_dec(x_28);
if (x_25 == 0)
{
uint8_t x_57; 
x_57 = 0;
x_30 = x_57;
goto block_56;
}
else
{
uint8_t x_58; 
x_58 = 1;
x_30 = x_58;
goto block_56;
}
block_56:
{
lean_object* x_31; 
if (x_21 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_42 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
x_43 = lean_box(0);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_42, x_43, x_10, x_11);
lean_dec(x_10);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
if (x_30 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_49 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
x_50 = lean_box(0);
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_49, x_50, x_10, x_11);
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_dec(x_5);
x_31 = x_11;
goto block_41;
}
}
block_41:
{
lean_object* x_32; 
lean_inc(x_10);
lean_inc(x_29);
x_32 = l_Lean_Meta_inferType(x_29, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed), 10, 6);
lean_closure_set(x_35, 0, x_29);
lean_closure_set(x_35, 1, x_6);
lean_closure_set(x_35, 2, x_1);
lean_closure_set(x_35, 3, x_2);
lean_closure_set(x_35, 4, x_3);
lean_closure_set(x_35, 5, x_27);
x_36 = l_Lean_Meta_forallTelescopeReducing___rarg(x_33, x_35, x_10, x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_59 = l_Lean_Meta_mkNoConfusion___closed__8;
x_60 = lean_box(0);
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_59, x_60, x_10, x_11);
lean_dec(x_10);
return x_61;
}
}
}
case 5:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_dec(x_7);
x_64 = lean_array_set(x_8, x_9, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_sub(x_9, x_65);
lean_dec(x_9);
x_7 = x_62;
x_8 = x_64;
x_9 = x_66;
goto _start;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = l_Lean_Meta_mkNoConfusion___closed__8;
x_69 = lean_box(0);
x_70 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_68, x_69, x_10, x_11);
lean_dec(x_10);
return x_70;
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_26 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(x_4, x_14, x_18, x_23, x_25, x_2, x_19);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2(x_1, x_8, x_8, x_8);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8(x_1, x_2, x_3, x_10);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__10(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__7(x_1, x_2, x_3, x_20);
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
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_35, x_51);
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
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_71, x_86);
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
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_104, x_119);
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
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_137, x_181);
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
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_138, x_155);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14(x_1, x_2, x_3, x_10);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13(x_1, x_2, x_3, x_20);
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
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_35, x_51);
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
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_71, x_86);
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
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_104, x_119);
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
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_137, x_181);
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
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_138, x_155);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20(x_1, x_2, x_3, x_10);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__22(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19(x_1, x_2, x_3, x_20);
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
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_35, x_51);
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
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_71, x_86);
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
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_104, x_119);
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
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_137, x_181);
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
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_138, x_155);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26(x_1, x_2, x_3, x_10);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25(x_1, x_2, x_3, x_20);
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
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_35, x_51);
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
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_71, x_86);
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
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_104, x_119);
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
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_137, x_181);
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
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_138, x_155);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32(x_1, x_2, x_3, x_10);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__33(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31(x_1, x_2, x_3, x_20);
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
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_35, x_51);
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
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_71, x_86);
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
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_104, x_119);
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
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_137, x_181);
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
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_138, x_155);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38(x_1, x_2, x_3, x_10);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39(x_1, x_2, x_3, x_5, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__40(x_1, x_2, x_3, x_9, x_9, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_15, x_2, x_3, x_16);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38(x_1, x_2, x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_7, x_2, x_3, x_8);
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
x_21 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37(x_1, x_2, x_3, x_20);
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
x_52 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_35, x_51);
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
x_87 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_71, x_86);
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
x_120 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_104, x_119);
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
x_182 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_137, x_181);
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
x_156 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_138, x_155);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__44(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_11);
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4(x_1, x_16, x_2, x_3, x_20);
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
x_27 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_22, x_26);
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
x_35 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_22, x_34);
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
x_72 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_42, x_71);
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
x_77 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_42, x_76);
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
x_49 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_43, x_45);
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
x_56 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_43, x_45);
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
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__44(x_1, x_2, x_3, x_4, x_6, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_10, x_10, x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4(x_1, x_16, x_2, x_3, x_20);
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
x_27 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_22, x_26);
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
x_35 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_22, x_34);
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
x_72 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_42, x_71);
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
x_77 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_42, x_76);
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
x_49 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_43, x_45);
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
x_56 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_43, x_45);
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
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_4);
x_7 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1(x_1, x_4, x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_6);
x_9 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3(x_4, x_6, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
x_13 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42(x_1, x_4, x_6, x_11, x_12);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__35(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__40(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__41(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__44(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_10);
x_19 = l_Lean_Meta_FVarSubst_get(x_18, x_10);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_6);
x_21 = l_Lean_Meta_clear(x_16, x_20, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_4, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_10, x_18);
lean_dec(x_10);
lean_ctor_set(x_13, 2, x_27);
lean_ctor_set(x_13, 0, x_25);
x_3 = x_12;
x_6 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_10, x_18);
lean_dec(x_10);
lean_ctor_set(x_13, 2, x_31);
lean_ctor_set(x_13, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_14);
x_3 = x_12;
x_4 = x_32;
x_6 = x_30;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_13);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_6, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 5);
lean_inc(x_37);
lean_dec(x_6);
x_38 = l_Lean_Meta_restore(x_35, x_36, x_37, x_5, x_34);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_3 = x_12;
x_6 = x_39;
goto _start;
}
}
else
{
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
x_3 = x_12;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
x_44 = lean_ctor_get(x_13, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
lean_inc(x_10);
x_45 = l_Lean_Meta_FVarSubst_get(x_44, x_10);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_6);
x_47 = l_Lean_Meta_clear(x_42, x_46, x_5, x_6);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_48 = x_4;
} else {
 lean_dec_ref(x_4);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_10, x_44);
lean_dec(x_10);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_51);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_14);
x_3 = x_12;
x_4 = x_53;
x_6 = x_50;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_14);
lean_dec(x_10);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_ctor_get(x_6, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_6, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_6, 5);
lean_inc(x_58);
lean_dec(x_6);
x_59 = l_Lean_Meta_restore(x_56, x_57, x_58, x_5, x_55);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_3 = x_12;
x_6 = x_60;
goto _start;
}
}
else
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_14);
lean_dec(x_10);
x_3 = x_12;
goto _start;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_15 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(x_1, x_2, x_12, x_14, x_5, x_6);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = x_2;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2___boxed), 6, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
x_9 = x_8;
x_10 = lean_apply_2(x_9, x_3, x_4);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l_Lean_Name_inhabited;
x_15 = lean_array_get(x_14, x_1, x_5);
lean_inc(x_3);
lean_inc(x_15);
x_16 = l_Lean_mkConst(x_15, x_3);
x_17 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_11, x_16);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_13, 2);
x_21 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_19, x_19, x_11, x_17);
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
x_32 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_30, x_30, x_11, x_17);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = x_1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1(x_2, x_3, x_4, x_5, x_7, x_6);
x_9 = x_8;
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cases");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2;
x_17 = l_Lean_Meta_mkNoConfusion___closed__5;
x_18 = lean_box(0);
x_19 = l_Lean_Meta_throwTacticEx___rarg(x_16, x_1, x_17, x_18, x_7, x_8);
lean_dec(x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Expr_appFn_x21(x_9);
x_21 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_22 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_22);
lean_inc(x_21);
x_23 = l_Lean_Meta_isExprDefEq(x_21, x_22, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_7);
lean_inc(x_21);
x_27 = l_Lean_Meta_whnf(x_21, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_22);
x_30 = l_Lean_Meta_whnf(x_22, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_expr_eqv(x_28, x_21);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_2);
x_34 = l_Lean_mkFVar(x_2);
lean_inc(x_7);
x_35 = l_Lean_Meta_mkEq(x_28, x_31, x_7, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_LocalDecl_userName(x_6);
x_39 = l_Lean_Meta_assert(x_1, x_38, x_36, x_34, x_7, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_clear(x_40, x_2, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_3, x_45);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 2);
lean_inc(x_48);
lean_dec(x_4);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_5);
x_51 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_46, x_50, x_7, x_44);
lean_dec(x_7);
lean_dec(x_46);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
return x_39;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
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
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_35);
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
x_64 = lean_expr_eqv(x_31, x_22);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_2);
x_65 = l_Lean_mkFVar(x_2);
lean_inc(x_7);
x_66 = l_Lean_Meta_mkEq(x_28, x_31, x_7, x_32);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_LocalDecl_userName(x_6);
x_70 = l_Lean_Meta_assert(x_1, x_69, x_67, x_65, x_7, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_clear(x_71, x_2, x_7, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_3, x_76);
x_78 = lean_ctor_get(x_4, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 2);
lean_inc(x_79);
lean_dec(x_4);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_5);
x_82 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_77, x_81, x_7, x_75);
lean_dec(x_7);
lean_dec(x_77);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_73);
if (x_83 == 0)
{
return x_73;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_73, 0);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_73);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_70);
if (x_87 == 0)
{
return x_70;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_70, 0);
x_89 = lean_ctor_get(x_70, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_70);
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
lean_dec(x_65);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_66);
if (x_91 == 0)
{
return x_66;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_66, 0);
x_93 = lean_ctor_get(x_66, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_66);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_28);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; 
lean_dec(x_22);
x_95 = lean_ctor_get(x_4, 2);
lean_inc(x_95);
x_96 = 1;
x_97 = l_Lean_Meta_substCore(x_1, x_2, x_96, x_95, x_96, x_7, x_32);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_4, 1);
lean_inc(x_102);
lean_dec(x_4);
x_103 = x_102;
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1(x_100, x_104, x_103);
x_106 = x_105;
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_100);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_5);
x_109 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_108, x_7, x_99);
lean_dec(x_7);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_97);
if (x_110 == 0)
{
return x_97;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_97, 0);
x_112 = lean_ctor_get(x_97, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_97);
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
lean_dec(x_22);
x_114 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
lean_dec(x_7);
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
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
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
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_4, 2);
lean_inc(x_127);
lean_dec(x_4);
x_128 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_5);
x_130 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_125, x_129, x_7, x_122);
lean_dec(x_7);
lean_dec(x_125);
return x_130;
}
}
else
{
uint8_t x_131; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_131 = !lean_is_exclusive(x_114);
if (x_131 == 0)
{
return x_114;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_114, 0);
x_133 = lean_ctor_get(x_114, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_114);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
case 1:
{
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; 
lean_dec(x_22);
lean_dec(x_21);
x_135 = lean_ctor_get(x_4, 2);
lean_inc(x_135);
x_136 = 1;
x_137 = lean_unbox(x_24);
lean_dec(x_24);
x_138 = l_Lean_Meta_substCore(x_1, x_2, x_137, x_135, x_136, x_7, x_32);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_ctor_get(x_4, 1);
lean_inc(x_143);
lean_dec(x_4);
x_144 = x_143;
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2(x_141, x_145, x_144);
x_147 = x_146;
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_141);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_5);
x_150 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_149, x_7, x_140);
lean_dec(x_7);
return x_150;
}
else
{
uint8_t x_151; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_151 = !lean_is_exclusive(x_138);
if (x_151 == 0)
{
return x_138;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_138, 0);
x_153 = lean_ctor_get(x_138, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_138);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
case 1:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_24);
x_155 = lean_ctor_get(x_21, 0);
lean_inc(x_155);
lean_dec(x_21);
x_156 = lean_ctor_get(x_22, 0);
lean_inc(x_156);
lean_dec(x_22);
lean_inc(x_7);
x_157 = l_Lean_Meta_getLocalDecl(x_155, x_7, x_32);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_7);
x_160 = l_Lean_Meta_getLocalDecl(x_156, x_7, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lean_LocalDecl_index(x_158);
lean_dec(x_158);
x_164 = l_Lean_LocalDecl_index(x_161);
lean_dec(x_161);
x_165 = lean_nat_dec_lt(x_163, x_164);
lean_dec(x_164);
lean_dec(x_163);
x_166 = lean_ctor_get(x_4, 2);
lean_inc(x_166);
x_167 = 1;
x_168 = l_Lean_Meta_substCore(x_1, x_2, x_165, x_166, x_167, x_7, x_162);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_ctor_get(x_4, 1);
lean_inc(x_173);
lean_dec(x_4);
x_174 = x_173;
x_175 = lean_unsigned_to_nat(0u);
x_176 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3(x_171, x_175, x_174);
x_177 = x_176;
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_171);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_5);
x_180 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_179, x_7, x_170);
lean_dec(x_7);
return x_180;
}
else
{
uint8_t x_181; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_181 = !lean_is_exclusive(x_168);
if (x_181 == 0)
{
return x_168;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_168, 0);
x_183 = lean_ctor_get(x_168, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_168);
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
lean_dec(x_158);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_160);
if (x_185 == 0)
{
return x_160;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_160, 0);
x_187 = lean_ctor_get(x_160, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_160);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_156);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_157);
if (x_189 == 0)
{
return x_157;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_157, 0);
x_191 = lean_ctor_get(x_157, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_157);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 2:
{
lean_object* x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; 
lean_dec(x_22);
lean_dec(x_21);
x_193 = lean_ctor_get(x_4, 2);
lean_inc(x_193);
x_194 = 1;
x_195 = lean_unbox(x_24);
lean_dec(x_24);
x_196 = l_Lean_Meta_substCore(x_1, x_2, x_195, x_193, x_194, x_7, x_32);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec(x_197);
x_201 = lean_ctor_get(x_4, 1);
lean_inc(x_201);
lean_dec(x_4);
x_202 = x_201;
x_203 = lean_unsigned_to_nat(0u);
x_204 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4(x_199, x_203, x_202);
x_205 = x_204;
x_206 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_206, 0, x_200);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_199);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_5);
x_208 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_207, x_7, x_198);
lean_dec(x_7);
return x_208;
}
else
{
uint8_t x_209; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_209 = !lean_is_exclusive(x_196);
if (x_209 == 0)
{
return x_196;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_196, 0);
x_211 = lean_ctor_get(x_196, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_196);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
case 3:
{
lean_object* x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; 
lean_dec(x_22);
lean_dec(x_21);
x_213 = lean_ctor_get(x_4, 2);
lean_inc(x_213);
x_214 = 1;
x_215 = lean_unbox(x_24);
lean_dec(x_24);
x_216 = l_Lean_Meta_substCore(x_1, x_2, x_215, x_213, x_214, x_7, x_32);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_ctor_get(x_4, 1);
lean_inc(x_221);
lean_dec(x_4);
x_222 = x_221;
x_223 = lean_unsigned_to_nat(0u);
x_224 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5(x_219, x_223, x_222);
x_225 = x_224;
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_220);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_226, 2, x_219);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_5);
x_228 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_227, x_7, x_218);
lean_dec(x_7);
return x_228;
}
else
{
uint8_t x_229; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_229 = !lean_is_exclusive(x_216);
if (x_229 == 0)
{
return x_216;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_216, 0);
x_231 = lean_ctor_get(x_216, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_216);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
case 4:
{
lean_object* x_233; uint8_t x_234; uint8_t x_235; lean_object* x_236; 
lean_dec(x_22);
lean_dec(x_21);
x_233 = lean_ctor_get(x_4, 2);
lean_inc(x_233);
x_234 = 1;
x_235 = lean_unbox(x_24);
lean_dec(x_24);
x_236 = l_Lean_Meta_substCore(x_1, x_2, x_235, x_233, x_234, x_7, x_32);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get(x_4, 1);
lean_inc(x_241);
lean_dec(x_4);
x_242 = x_241;
x_243 = lean_unsigned_to_nat(0u);
x_244 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6(x_239, x_243, x_242);
x_245 = x_244;
x_246 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_246, 0, x_240);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_239);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_5);
x_248 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_247, x_7, x_238);
lean_dec(x_7);
return x_248;
}
else
{
uint8_t x_249; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_249 = !lean_is_exclusive(x_236);
if (x_249 == 0)
{
return x_236;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_236, 0);
x_251 = lean_ctor_get(x_236, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_236);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
case 5:
{
lean_object* x_253; uint8_t x_254; uint8_t x_255; lean_object* x_256; 
lean_dec(x_22);
lean_dec(x_21);
x_253 = lean_ctor_get(x_4, 2);
lean_inc(x_253);
x_254 = 1;
x_255 = lean_unbox(x_24);
lean_dec(x_24);
x_256 = l_Lean_Meta_substCore(x_1, x_2, x_255, x_253, x_254, x_7, x_32);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec(x_257);
x_261 = lean_ctor_get(x_4, 1);
lean_inc(x_261);
lean_dec(x_4);
x_262 = x_261;
x_263 = lean_unsigned_to_nat(0u);
x_264 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7(x_259, x_263, x_262);
x_265 = x_264;
x_266 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_266, 0, x_260);
lean_ctor_set(x_266, 1, x_265);
lean_ctor_set(x_266, 2, x_259);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_5);
x_268 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_267, x_7, x_258);
lean_dec(x_7);
return x_268;
}
else
{
uint8_t x_269; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_269 = !lean_is_exclusive(x_256);
if (x_269 == 0)
{
return x_256;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_256, 0);
x_271 = lean_ctor_get(x_256, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_256);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
case 6:
{
lean_object* x_273; uint8_t x_274; uint8_t x_275; lean_object* x_276; 
lean_dec(x_22);
lean_dec(x_21);
x_273 = lean_ctor_get(x_4, 2);
lean_inc(x_273);
x_274 = 1;
x_275 = lean_unbox(x_24);
lean_dec(x_24);
x_276 = l_Lean_Meta_substCore(x_1, x_2, x_275, x_273, x_274, x_7, x_32);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
lean_dec(x_277);
x_281 = lean_ctor_get(x_4, 1);
lean_inc(x_281);
lean_dec(x_4);
x_282 = x_281;
x_283 = lean_unsigned_to_nat(0u);
x_284 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8(x_279, x_283, x_282);
x_285 = x_284;
x_286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_286, 0, x_280);
lean_ctor_set(x_286, 1, x_285);
lean_ctor_set(x_286, 2, x_279);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_5);
x_288 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_287, x_7, x_278);
lean_dec(x_7);
return x_288;
}
else
{
uint8_t x_289; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_289 = !lean_is_exclusive(x_276);
if (x_289 == 0)
{
return x_276;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_276, 0);
x_291 = lean_ctor_get(x_276, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_276);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
case 7:
{
lean_object* x_293; uint8_t x_294; uint8_t x_295; lean_object* x_296; 
lean_dec(x_22);
lean_dec(x_21);
x_293 = lean_ctor_get(x_4, 2);
lean_inc(x_293);
x_294 = 1;
x_295 = lean_unbox(x_24);
lean_dec(x_24);
x_296 = l_Lean_Meta_substCore(x_1, x_2, x_295, x_293, x_294, x_7, x_32);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_ctor_get(x_4, 1);
lean_inc(x_301);
lean_dec(x_4);
x_302 = x_301;
x_303 = lean_unsigned_to_nat(0u);
x_304 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9(x_299, x_303, x_302);
x_305 = x_304;
x_306 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_306, 0, x_300);
lean_ctor_set(x_306, 1, x_305);
lean_ctor_set(x_306, 2, x_299);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_5);
x_308 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_307, x_7, x_298);
lean_dec(x_7);
return x_308;
}
else
{
uint8_t x_309; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_309 = !lean_is_exclusive(x_296);
if (x_309 == 0)
{
return x_296;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_296, 0);
x_311 = lean_ctor_get(x_296, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_296);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
case 8:
{
lean_object* x_313; uint8_t x_314; uint8_t x_315; lean_object* x_316; 
lean_dec(x_22);
lean_dec(x_21);
x_313 = lean_ctor_get(x_4, 2);
lean_inc(x_313);
x_314 = 1;
x_315 = lean_unbox(x_24);
lean_dec(x_24);
x_316 = l_Lean_Meta_substCore(x_1, x_2, x_315, x_313, x_314, x_7, x_32);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = lean_ctor_get(x_4, 1);
lean_inc(x_321);
lean_dec(x_4);
x_322 = x_321;
x_323 = lean_unsigned_to_nat(0u);
x_324 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10(x_319, x_323, x_322);
x_325 = x_324;
x_326 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_326, 0, x_320);
lean_ctor_set(x_326, 1, x_325);
lean_ctor_set(x_326, 2, x_319);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_5);
x_328 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_327, x_7, x_318);
lean_dec(x_7);
return x_328;
}
else
{
uint8_t x_329; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_329 = !lean_is_exclusive(x_316);
if (x_329 == 0)
{
return x_316;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_316, 0);
x_331 = lean_ctor_get(x_316, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_316);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
case 9:
{
lean_object* x_333; uint8_t x_334; uint8_t x_335; lean_object* x_336; 
lean_dec(x_22);
lean_dec(x_21);
x_333 = lean_ctor_get(x_4, 2);
lean_inc(x_333);
x_334 = 1;
x_335 = lean_unbox(x_24);
lean_dec(x_24);
x_336 = l_Lean_Meta_substCore(x_1, x_2, x_335, x_333, x_334, x_7, x_32);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_ctor_get(x_337, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec(x_337);
x_341 = lean_ctor_get(x_4, 1);
lean_inc(x_341);
lean_dec(x_4);
x_342 = x_341;
x_343 = lean_unsigned_to_nat(0u);
x_344 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11(x_339, x_343, x_342);
x_345 = x_344;
x_346 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_346, 0, x_340);
lean_ctor_set(x_346, 1, x_345);
lean_ctor_set(x_346, 2, x_339);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_5);
x_348 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_347, x_7, x_338);
lean_dec(x_7);
return x_348;
}
else
{
uint8_t x_349; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_349 = !lean_is_exclusive(x_336);
if (x_349 == 0)
{
return x_336;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_336, 0);
x_351 = lean_ctor_get(x_336, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_336);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
case 10:
{
lean_object* x_353; uint8_t x_354; uint8_t x_355; lean_object* x_356; 
lean_dec(x_22);
lean_dec(x_21);
x_353 = lean_ctor_get(x_4, 2);
lean_inc(x_353);
x_354 = 1;
x_355 = lean_unbox(x_24);
lean_dec(x_24);
x_356 = l_Lean_Meta_substCore(x_1, x_2, x_355, x_353, x_354, x_7, x_32);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = lean_ctor_get(x_357, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_361 = lean_ctor_get(x_4, 1);
lean_inc(x_361);
lean_dec(x_4);
x_362 = x_361;
x_363 = lean_unsigned_to_nat(0u);
x_364 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12(x_359, x_363, x_362);
x_365 = x_364;
x_366 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_366, 0, x_360);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set(x_366, 2, x_359);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_5);
x_368 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_367, x_7, x_358);
lean_dec(x_7);
return x_368;
}
else
{
uint8_t x_369; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_369 = !lean_is_exclusive(x_356);
if (x_369 == 0)
{
return x_356;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_356, 0);
x_371 = lean_ctor_get(x_356, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_356);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
case 11:
{
lean_object* x_373; uint8_t x_374; uint8_t x_375; lean_object* x_376; 
lean_dec(x_22);
lean_dec(x_21);
x_373 = lean_ctor_get(x_4, 2);
lean_inc(x_373);
x_374 = 1;
x_375 = lean_unbox(x_24);
lean_dec(x_24);
x_376 = l_Lean_Meta_substCore(x_1, x_2, x_375, x_373, x_374, x_7, x_32);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_ctor_get(x_377, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
lean_dec(x_377);
x_381 = lean_ctor_get(x_4, 1);
lean_inc(x_381);
lean_dec(x_4);
x_382 = x_381;
x_383 = lean_unsigned_to_nat(0u);
x_384 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13(x_379, x_383, x_382);
x_385 = x_384;
x_386 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_385);
lean_ctor_set(x_386, 2, x_379);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_5);
x_388 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_387, x_7, x_378);
lean_dec(x_7);
return x_388;
}
else
{
uint8_t x_389; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_389 = !lean_is_exclusive(x_376);
if (x_389 == 0)
{
return x_376;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_376, 0);
x_391 = lean_ctor_get(x_376, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_376);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
default: 
{
lean_object* x_393; uint8_t x_394; uint8_t x_395; lean_object* x_396; 
lean_dec(x_22);
lean_dec(x_21);
x_393 = lean_ctor_get(x_4, 2);
lean_inc(x_393);
x_394 = 1;
x_395 = lean_unbox(x_24);
lean_dec(x_24);
x_396 = l_Lean_Meta_substCore(x_1, x_2, x_395, x_393, x_394, x_7, x_32);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 1);
lean_inc(x_400);
lean_dec(x_397);
x_401 = lean_ctor_get(x_4, 1);
lean_inc(x_401);
lean_dec(x_4);
x_402 = x_401;
x_403 = lean_unsigned_to_nat(0u);
x_404 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14(x_399, x_403, x_402);
x_405 = x_404;
x_406 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_406, 0, x_400);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set(x_406, 2, x_399);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_5);
x_408 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_407, x_7, x_398);
lean_dec(x_7);
return x_408;
}
else
{
uint8_t x_409; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_409 = !lean_is_exclusive(x_396);
if (x_409 == 0)
{
return x_396;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_396, 0);
x_411 = lean_ctor_get(x_396, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_396);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
}
}
case 2:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_413; uint8_t x_414; lean_object* x_415; 
lean_dec(x_22);
x_413 = lean_ctor_get(x_4, 2);
lean_inc(x_413);
x_414 = 1;
x_415 = l_Lean_Meta_substCore(x_1, x_2, x_414, x_413, x_414, x_7, x_32);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = lean_ctor_get(x_416, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
lean_dec(x_416);
x_420 = lean_ctor_get(x_4, 1);
lean_inc(x_420);
lean_dec(x_4);
x_421 = x_420;
x_422 = lean_unsigned_to_nat(0u);
x_423 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15(x_418, x_422, x_421);
x_424 = x_423;
x_425 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_425, 0, x_419);
lean_ctor_set(x_425, 1, x_424);
lean_ctor_set(x_425, 2, x_418);
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_5);
x_427 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_426, x_7, x_417);
lean_dec(x_7);
return x_427;
}
else
{
uint8_t x_428; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_428 = !lean_is_exclusive(x_415);
if (x_428 == 0)
{
return x_415;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_415, 0);
x_430 = lean_ctor_get(x_415, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_415);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
else
{
lean_object* x_432; 
lean_dec(x_22);
x_432 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
uint8_t x_434; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_434 = !lean_is_exclusive(x_432);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_ctor_get(x_432, 0);
lean_dec(x_435);
x_436 = lean_box(0);
lean_ctor_set(x_432, 0, x_436);
return x_432;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_432, 1);
lean_inc(x_437);
lean_dec(x_432);
x_438 = lean_box(0);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_440 = lean_ctor_get(x_432, 1);
lean_inc(x_440);
lean_dec(x_432);
x_441 = lean_ctor_get(x_433, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_433, 1);
lean_inc(x_442);
lean_dec(x_433);
x_443 = lean_nat_add(x_3, x_442);
lean_dec(x_442);
x_444 = lean_ctor_get(x_4, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_4, 2);
lean_inc(x_445);
lean_dec(x_4);
x_446 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_446, 0, x_441);
lean_ctor_set(x_446, 1, x_444);
lean_ctor_set(x_446, 2, x_445);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_5);
x_448 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_443, x_447, x_7, x_440);
lean_dec(x_7);
lean_dec(x_443);
return x_448;
}
}
else
{
uint8_t x_449; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_449 = !lean_is_exclusive(x_432);
if (x_449 == 0)
{
return x_432;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_432, 0);
x_451 = lean_ctor_get(x_432, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_432);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
return x_452;
}
}
}
}
case 3:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_453; uint8_t x_454; lean_object* x_455; 
lean_dec(x_22);
x_453 = lean_ctor_get(x_4, 2);
lean_inc(x_453);
x_454 = 1;
x_455 = l_Lean_Meta_substCore(x_1, x_2, x_454, x_453, x_454, x_7, x_32);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_ctor_get(x_456, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_dec(x_456);
x_460 = lean_ctor_get(x_4, 1);
lean_inc(x_460);
lean_dec(x_4);
x_461 = x_460;
x_462 = lean_unsigned_to_nat(0u);
x_463 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16(x_458, x_462, x_461);
x_464 = x_463;
x_465 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_465, 0, x_459);
lean_ctor_set(x_465, 1, x_464);
lean_ctor_set(x_465, 2, x_458);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_5);
x_467 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_466, x_7, x_457);
lean_dec(x_7);
return x_467;
}
else
{
uint8_t x_468; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_468 = !lean_is_exclusive(x_455);
if (x_468 == 0)
{
return x_455;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_455, 0);
x_470 = lean_ctor_get(x_455, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_455);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
else
{
lean_object* x_472; 
lean_dec(x_22);
x_472 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_474 = !lean_is_exclusive(x_472);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_472, 0);
lean_dec(x_475);
x_476 = lean_box(0);
lean_ctor_set(x_472, 0, x_476);
return x_472;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_472, 1);
lean_inc(x_477);
lean_dec(x_472);
x_478 = lean_box(0);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_480 = lean_ctor_get(x_472, 1);
lean_inc(x_480);
lean_dec(x_472);
x_481 = lean_ctor_get(x_473, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_473, 1);
lean_inc(x_482);
lean_dec(x_473);
x_483 = lean_nat_add(x_3, x_482);
lean_dec(x_482);
x_484 = lean_ctor_get(x_4, 1);
lean_inc(x_484);
x_485 = lean_ctor_get(x_4, 2);
lean_inc(x_485);
lean_dec(x_4);
x_486 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_484);
lean_ctor_set(x_486, 2, x_485);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_5);
x_488 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_483, x_487, x_7, x_480);
lean_dec(x_7);
lean_dec(x_483);
return x_488;
}
}
else
{
uint8_t x_489; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_489 = !lean_is_exclusive(x_472);
if (x_489 == 0)
{
return x_472;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_472, 0);
x_491 = lean_ctor_get(x_472, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_472);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
}
case 4:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_493; uint8_t x_494; lean_object* x_495; 
lean_dec(x_22);
x_493 = lean_ctor_get(x_4, 2);
lean_inc(x_493);
x_494 = 1;
x_495 = l_Lean_Meta_substCore(x_1, x_2, x_494, x_493, x_494, x_7, x_32);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_ctor_get(x_496, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_496, 1);
lean_inc(x_499);
lean_dec(x_496);
x_500 = lean_ctor_get(x_4, 1);
lean_inc(x_500);
lean_dec(x_4);
x_501 = x_500;
x_502 = lean_unsigned_to_nat(0u);
x_503 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17(x_498, x_502, x_501);
x_504 = x_503;
x_505 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_504);
lean_ctor_set(x_505, 2, x_498);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_5);
x_507 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_506, x_7, x_497);
lean_dec(x_7);
return x_507;
}
else
{
uint8_t x_508; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_508 = !lean_is_exclusive(x_495);
if (x_508 == 0)
{
return x_495;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_495, 0);
x_510 = lean_ctor_get(x_495, 1);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_495);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
}
else
{
lean_object* x_512; 
lean_dec(x_22);
x_512 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
if (lean_obj_tag(x_513) == 0)
{
uint8_t x_514; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_514 = !lean_is_exclusive(x_512);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_512, 0);
lean_dec(x_515);
x_516 = lean_box(0);
lean_ctor_set(x_512, 0, x_516);
return x_512;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_512, 1);
lean_inc(x_517);
lean_dec(x_512);
x_518 = lean_box(0);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_520 = lean_ctor_get(x_512, 1);
lean_inc(x_520);
lean_dec(x_512);
x_521 = lean_ctor_get(x_513, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_513, 1);
lean_inc(x_522);
lean_dec(x_513);
x_523 = lean_nat_add(x_3, x_522);
lean_dec(x_522);
x_524 = lean_ctor_get(x_4, 1);
lean_inc(x_524);
x_525 = lean_ctor_get(x_4, 2);
lean_inc(x_525);
lean_dec(x_4);
x_526 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_526, 0, x_521);
lean_ctor_set(x_526, 1, x_524);
lean_ctor_set(x_526, 2, x_525);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_5);
x_528 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_523, x_527, x_7, x_520);
lean_dec(x_7);
lean_dec(x_523);
return x_528;
}
}
else
{
uint8_t x_529; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_529 = !lean_is_exclusive(x_512);
if (x_529 == 0)
{
return x_512;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_512, 0);
x_531 = lean_ctor_get(x_512, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_512);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
}
case 5:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_533; uint8_t x_534; lean_object* x_535; 
lean_dec(x_22);
x_533 = lean_ctor_get(x_4, 2);
lean_inc(x_533);
x_534 = 1;
x_535 = l_Lean_Meta_substCore(x_1, x_2, x_534, x_533, x_534, x_7, x_32);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_ctor_get(x_536, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_536, 1);
lean_inc(x_539);
lean_dec(x_536);
x_540 = lean_ctor_get(x_4, 1);
lean_inc(x_540);
lean_dec(x_4);
x_541 = x_540;
x_542 = lean_unsigned_to_nat(0u);
x_543 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18(x_538, x_542, x_541);
x_544 = x_543;
x_545 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_545, 0, x_539);
lean_ctor_set(x_545, 1, x_544);
lean_ctor_set(x_545, 2, x_538);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_5);
x_547 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_546, x_7, x_537);
lean_dec(x_7);
return x_547;
}
else
{
uint8_t x_548; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_548 = !lean_is_exclusive(x_535);
if (x_548 == 0)
{
return x_535;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_535, 0);
x_550 = lean_ctor_get(x_535, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_535);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
return x_551;
}
}
}
else
{
lean_object* x_552; 
lean_dec(x_22);
x_552 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
if (lean_obj_tag(x_553) == 0)
{
uint8_t x_554; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_554 = !lean_is_exclusive(x_552);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_552, 0);
lean_dec(x_555);
x_556 = lean_box(0);
lean_ctor_set(x_552, 0, x_556);
return x_552;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_552, 1);
lean_inc(x_557);
lean_dec(x_552);
x_558 = lean_box(0);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_557);
return x_559;
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_560 = lean_ctor_get(x_552, 1);
lean_inc(x_560);
lean_dec(x_552);
x_561 = lean_ctor_get(x_553, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_553, 1);
lean_inc(x_562);
lean_dec(x_553);
x_563 = lean_nat_add(x_3, x_562);
lean_dec(x_562);
x_564 = lean_ctor_get(x_4, 1);
lean_inc(x_564);
x_565 = lean_ctor_get(x_4, 2);
lean_inc(x_565);
lean_dec(x_4);
x_566 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_566, 0, x_561);
lean_ctor_set(x_566, 1, x_564);
lean_ctor_set(x_566, 2, x_565);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_5);
x_568 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_563, x_567, x_7, x_560);
lean_dec(x_7);
lean_dec(x_563);
return x_568;
}
}
else
{
uint8_t x_569; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_569 = !lean_is_exclusive(x_552);
if (x_569 == 0)
{
return x_552;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_552, 0);
x_571 = lean_ctor_get(x_552, 1);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_552);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_570);
lean_ctor_set(x_572, 1, x_571);
return x_572;
}
}
}
}
case 6:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_573; uint8_t x_574; lean_object* x_575; 
lean_dec(x_22);
x_573 = lean_ctor_get(x_4, 2);
lean_inc(x_573);
x_574 = 1;
x_575 = l_Lean_Meta_substCore(x_1, x_2, x_574, x_573, x_574, x_7, x_32);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
lean_dec(x_575);
x_578 = lean_ctor_get(x_576, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_576, 1);
lean_inc(x_579);
lean_dec(x_576);
x_580 = lean_ctor_get(x_4, 1);
lean_inc(x_580);
lean_dec(x_4);
x_581 = x_580;
x_582 = lean_unsigned_to_nat(0u);
x_583 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19(x_578, x_582, x_581);
x_584 = x_583;
x_585 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_585, 0, x_579);
lean_ctor_set(x_585, 1, x_584);
lean_ctor_set(x_585, 2, x_578);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_5);
x_587 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_586, x_7, x_577);
lean_dec(x_7);
return x_587;
}
else
{
uint8_t x_588; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_588 = !lean_is_exclusive(x_575);
if (x_588 == 0)
{
return x_575;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_575, 0);
x_590 = lean_ctor_get(x_575, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_575);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
}
else
{
lean_object* x_592; 
lean_dec(x_22);
x_592 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
if (lean_obj_tag(x_593) == 0)
{
uint8_t x_594; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_594 = !lean_is_exclusive(x_592);
if (x_594 == 0)
{
lean_object* x_595; lean_object* x_596; 
x_595 = lean_ctor_get(x_592, 0);
lean_dec(x_595);
x_596 = lean_box(0);
lean_ctor_set(x_592, 0, x_596);
return x_592;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_592, 1);
lean_inc(x_597);
lean_dec(x_592);
x_598 = lean_box(0);
x_599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_597);
return x_599;
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_600 = lean_ctor_get(x_592, 1);
lean_inc(x_600);
lean_dec(x_592);
x_601 = lean_ctor_get(x_593, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_593, 1);
lean_inc(x_602);
lean_dec(x_593);
x_603 = lean_nat_add(x_3, x_602);
lean_dec(x_602);
x_604 = lean_ctor_get(x_4, 1);
lean_inc(x_604);
x_605 = lean_ctor_get(x_4, 2);
lean_inc(x_605);
lean_dec(x_4);
x_606 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_606, 0, x_601);
lean_ctor_set(x_606, 1, x_604);
lean_ctor_set(x_606, 2, x_605);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_5);
x_608 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_603, x_607, x_7, x_600);
lean_dec(x_7);
lean_dec(x_603);
return x_608;
}
}
else
{
uint8_t x_609; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_609 = !lean_is_exclusive(x_592);
if (x_609 == 0)
{
return x_592;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_592, 0);
x_611 = lean_ctor_get(x_592, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_592);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
return x_612;
}
}
}
}
case 7:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_613; uint8_t x_614; lean_object* x_615; 
lean_dec(x_22);
x_613 = lean_ctor_get(x_4, 2);
lean_inc(x_613);
x_614 = 1;
x_615 = l_Lean_Meta_substCore(x_1, x_2, x_614, x_613, x_614, x_7, x_32);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec(x_615);
x_618 = lean_ctor_get(x_616, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_616, 1);
lean_inc(x_619);
lean_dec(x_616);
x_620 = lean_ctor_get(x_4, 1);
lean_inc(x_620);
lean_dec(x_4);
x_621 = x_620;
x_622 = lean_unsigned_to_nat(0u);
x_623 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20(x_618, x_622, x_621);
x_624 = x_623;
x_625 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_625, 0, x_619);
lean_ctor_set(x_625, 1, x_624);
lean_ctor_set(x_625, 2, x_618);
x_626 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_5);
x_627 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_626, x_7, x_617);
lean_dec(x_7);
return x_627;
}
else
{
uint8_t x_628; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_628 = !lean_is_exclusive(x_615);
if (x_628 == 0)
{
return x_615;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_615, 0);
x_630 = lean_ctor_get(x_615, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_615);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
else
{
lean_object* x_632; 
lean_dec(x_22);
x_632 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
if (lean_obj_tag(x_633) == 0)
{
uint8_t x_634; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_634 = !lean_is_exclusive(x_632);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_ctor_get(x_632, 0);
lean_dec(x_635);
x_636 = lean_box(0);
lean_ctor_set(x_632, 0, x_636);
return x_632;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_632, 1);
lean_inc(x_637);
lean_dec(x_632);
x_638 = lean_box(0);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_640 = lean_ctor_get(x_632, 1);
lean_inc(x_640);
lean_dec(x_632);
x_641 = lean_ctor_get(x_633, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_633, 1);
lean_inc(x_642);
lean_dec(x_633);
x_643 = lean_nat_add(x_3, x_642);
lean_dec(x_642);
x_644 = lean_ctor_get(x_4, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_4, 2);
lean_inc(x_645);
lean_dec(x_4);
x_646 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_646, 0, x_641);
lean_ctor_set(x_646, 1, x_644);
lean_ctor_set(x_646, 2, x_645);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_5);
x_648 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_643, x_647, x_7, x_640);
lean_dec(x_7);
lean_dec(x_643);
return x_648;
}
}
else
{
uint8_t x_649; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_649 = !lean_is_exclusive(x_632);
if (x_649 == 0)
{
return x_632;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_632, 0);
x_651 = lean_ctor_get(x_632, 1);
lean_inc(x_651);
lean_inc(x_650);
lean_dec(x_632);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_650);
lean_ctor_set(x_652, 1, x_651);
return x_652;
}
}
}
}
case 8:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_653; uint8_t x_654; lean_object* x_655; 
lean_dec(x_22);
x_653 = lean_ctor_get(x_4, 2);
lean_inc(x_653);
x_654 = 1;
x_655 = l_Lean_Meta_substCore(x_1, x_2, x_654, x_653, x_654, x_7, x_32);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_658 = lean_ctor_get(x_656, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_656, 1);
lean_inc(x_659);
lean_dec(x_656);
x_660 = lean_ctor_get(x_4, 1);
lean_inc(x_660);
lean_dec(x_4);
x_661 = x_660;
x_662 = lean_unsigned_to_nat(0u);
x_663 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21(x_658, x_662, x_661);
x_664 = x_663;
x_665 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_665, 0, x_659);
lean_ctor_set(x_665, 1, x_664);
lean_ctor_set(x_665, 2, x_658);
x_666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_5);
x_667 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_666, x_7, x_657);
lean_dec(x_7);
return x_667;
}
else
{
uint8_t x_668; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_668 = !lean_is_exclusive(x_655);
if (x_668 == 0)
{
return x_655;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_655, 0);
x_670 = lean_ctor_get(x_655, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_655);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
return x_671;
}
}
}
else
{
lean_object* x_672; 
lean_dec(x_22);
x_672 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; 
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
if (lean_obj_tag(x_673) == 0)
{
uint8_t x_674; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_674 = !lean_is_exclusive(x_672);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_672, 0);
lean_dec(x_675);
x_676 = lean_box(0);
lean_ctor_set(x_672, 0, x_676);
return x_672;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_672, 1);
lean_inc(x_677);
lean_dec(x_672);
x_678 = lean_box(0);
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_678);
lean_ctor_set(x_679, 1, x_677);
return x_679;
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_680 = lean_ctor_get(x_672, 1);
lean_inc(x_680);
lean_dec(x_672);
x_681 = lean_ctor_get(x_673, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_673, 1);
lean_inc(x_682);
lean_dec(x_673);
x_683 = lean_nat_add(x_3, x_682);
lean_dec(x_682);
x_684 = lean_ctor_get(x_4, 1);
lean_inc(x_684);
x_685 = lean_ctor_get(x_4, 2);
lean_inc(x_685);
lean_dec(x_4);
x_686 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_686, 0, x_681);
lean_ctor_set(x_686, 1, x_684);
lean_ctor_set(x_686, 2, x_685);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_5);
x_688 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_683, x_687, x_7, x_680);
lean_dec(x_7);
lean_dec(x_683);
return x_688;
}
}
else
{
uint8_t x_689; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_689 = !lean_is_exclusive(x_672);
if (x_689 == 0)
{
return x_672;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_690 = lean_ctor_get(x_672, 0);
x_691 = lean_ctor_get(x_672, 1);
lean_inc(x_691);
lean_inc(x_690);
lean_dec(x_672);
x_692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_692, 0, x_690);
lean_ctor_set(x_692, 1, x_691);
return x_692;
}
}
}
}
case 9:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_693; uint8_t x_694; lean_object* x_695; 
lean_dec(x_22);
x_693 = lean_ctor_get(x_4, 2);
lean_inc(x_693);
x_694 = 1;
x_695 = l_Lean_Meta_substCore(x_1, x_2, x_694, x_693, x_694, x_7, x_32);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_ctor_get(x_696, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_696, 1);
lean_inc(x_699);
lean_dec(x_696);
x_700 = lean_ctor_get(x_4, 1);
lean_inc(x_700);
lean_dec(x_4);
x_701 = x_700;
x_702 = lean_unsigned_to_nat(0u);
x_703 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22(x_698, x_702, x_701);
x_704 = x_703;
x_705 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_705, 0, x_699);
lean_ctor_set(x_705, 1, x_704);
lean_ctor_set(x_705, 2, x_698);
x_706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_5);
x_707 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_706, x_7, x_697);
lean_dec(x_7);
return x_707;
}
else
{
uint8_t x_708; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_708 = !lean_is_exclusive(x_695);
if (x_708 == 0)
{
return x_695;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_695, 0);
x_710 = lean_ctor_get(x_695, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_695);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
else
{
lean_object* x_712; 
lean_dec(x_22);
x_712 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
if (lean_obj_tag(x_713) == 0)
{
uint8_t x_714; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_714 = !lean_is_exclusive(x_712);
if (x_714 == 0)
{
lean_object* x_715; lean_object* x_716; 
x_715 = lean_ctor_get(x_712, 0);
lean_dec(x_715);
x_716 = lean_box(0);
lean_ctor_set(x_712, 0, x_716);
return x_712;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_712, 1);
lean_inc(x_717);
lean_dec(x_712);
x_718 = lean_box(0);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_717);
return x_719;
}
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_720 = lean_ctor_get(x_712, 1);
lean_inc(x_720);
lean_dec(x_712);
x_721 = lean_ctor_get(x_713, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_713, 1);
lean_inc(x_722);
lean_dec(x_713);
x_723 = lean_nat_add(x_3, x_722);
lean_dec(x_722);
x_724 = lean_ctor_get(x_4, 1);
lean_inc(x_724);
x_725 = lean_ctor_get(x_4, 2);
lean_inc(x_725);
lean_dec(x_4);
x_726 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_726, 0, x_721);
lean_ctor_set(x_726, 1, x_724);
lean_ctor_set(x_726, 2, x_725);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_5);
x_728 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_723, x_727, x_7, x_720);
lean_dec(x_7);
lean_dec(x_723);
return x_728;
}
}
else
{
uint8_t x_729; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_729 = !lean_is_exclusive(x_712);
if (x_729 == 0)
{
return x_712;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_712, 0);
x_731 = lean_ctor_get(x_712, 1);
lean_inc(x_731);
lean_inc(x_730);
lean_dec(x_712);
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
}
}
}
case 10:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_733; uint8_t x_734; lean_object* x_735; 
lean_dec(x_22);
x_733 = lean_ctor_get(x_4, 2);
lean_inc(x_733);
x_734 = 1;
x_735 = l_Lean_Meta_substCore(x_1, x_2, x_734, x_733, x_734, x_7, x_32);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
x_738 = lean_ctor_get(x_736, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_736, 1);
lean_inc(x_739);
lean_dec(x_736);
x_740 = lean_ctor_get(x_4, 1);
lean_inc(x_740);
lean_dec(x_4);
x_741 = x_740;
x_742 = lean_unsigned_to_nat(0u);
x_743 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23(x_738, x_742, x_741);
x_744 = x_743;
x_745 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_745, 0, x_739);
lean_ctor_set(x_745, 1, x_744);
lean_ctor_set(x_745, 2, x_738);
x_746 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_5);
x_747 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_746, x_7, x_737);
lean_dec(x_7);
return x_747;
}
else
{
uint8_t x_748; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_748 = !lean_is_exclusive(x_735);
if (x_748 == 0)
{
return x_735;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_735, 0);
x_750 = lean_ctor_get(x_735, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_735);
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
lean_dec(x_22);
x_752 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
if (lean_obj_tag(x_753) == 0)
{
uint8_t x_754; 
lean_dec(x_7);
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
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
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
x_764 = lean_ctor_get(x_4, 1);
lean_inc(x_764);
x_765 = lean_ctor_get(x_4, 2);
lean_inc(x_765);
lean_dec(x_4);
x_766 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_766, 0, x_761);
lean_ctor_set(x_766, 1, x_764);
lean_ctor_set(x_766, 2, x_765);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_5);
x_768 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_763, x_767, x_7, x_760);
lean_dec(x_7);
lean_dec(x_763);
return x_768;
}
}
else
{
uint8_t x_769; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_769 = !lean_is_exclusive(x_752);
if (x_769 == 0)
{
return x_752;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_752, 0);
x_771 = lean_ctor_get(x_752, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_752);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
}
case 11:
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_773; uint8_t x_774; lean_object* x_775; 
lean_dec(x_22);
x_773 = lean_ctor_get(x_4, 2);
lean_inc(x_773);
x_774 = 1;
x_775 = l_Lean_Meta_substCore(x_1, x_2, x_774, x_773, x_774, x_7, x_32);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = lean_ctor_get(x_776, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_776, 1);
lean_inc(x_779);
lean_dec(x_776);
x_780 = lean_ctor_get(x_4, 1);
lean_inc(x_780);
lean_dec(x_4);
x_781 = x_780;
x_782 = lean_unsigned_to_nat(0u);
x_783 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24(x_778, x_782, x_781);
x_784 = x_783;
x_785 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_785, 0, x_779);
lean_ctor_set(x_785, 1, x_784);
lean_ctor_set(x_785, 2, x_778);
x_786 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_5);
x_787 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_786, x_7, x_777);
lean_dec(x_7);
return x_787;
}
else
{
uint8_t x_788; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_788 = !lean_is_exclusive(x_775);
if (x_788 == 0)
{
return x_775;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_ctor_get(x_775, 0);
x_790 = lean_ctor_get(x_775, 1);
lean_inc(x_790);
lean_inc(x_789);
lean_dec(x_775);
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_789);
lean_ctor_set(x_791, 1, x_790);
return x_791;
}
}
}
else
{
lean_object* x_792; 
lean_dec(x_22);
x_792 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
if (lean_obj_tag(x_793) == 0)
{
uint8_t x_794; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_794 = !lean_is_exclusive(x_792);
if (x_794 == 0)
{
lean_object* x_795; lean_object* x_796; 
x_795 = lean_ctor_get(x_792, 0);
lean_dec(x_795);
x_796 = lean_box(0);
lean_ctor_set(x_792, 0, x_796);
return x_792;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_792, 1);
lean_inc(x_797);
lean_dec(x_792);
x_798 = lean_box(0);
x_799 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_799, 0, x_798);
lean_ctor_set(x_799, 1, x_797);
return x_799;
}
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_800 = lean_ctor_get(x_792, 1);
lean_inc(x_800);
lean_dec(x_792);
x_801 = lean_ctor_get(x_793, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_793, 1);
lean_inc(x_802);
lean_dec(x_793);
x_803 = lean_nat_add(x_3, x_802);
lean_dec(x_802);
x_804 = lean_ctor_get(x_4, 1);
lean_inc(x_804);
x_805 = lean_ctor_get(x_4, 2);
lean_inc(x_805);
lean_dec(x_4);
x_806 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_806, 0, x_801);
lean_ctor_set(x_806, 1, x_804);
lean_ctor_set(x_806, 2, x_805);
x_807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_5);
x_808 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_803, x_807, x_7, x_800);
lean_dec(x_7);
lean_dec(x_803);
return x_808;
}
}
else
{
uint8_t x_809; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_809 = !lean_is_exclusive(x_792);
if (x_809 == 0)
{
return x_792;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_810 = lean_ctor_get(x_792, 0);
x_811 = lean_ctor_get(x_792, 1);
lean_inc(x_811);
lean_inc(x_810);
lean_dec(x_792);
x_812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_812, 0, x_810);
lean_ctor_set(x_812, 1, x_811);
return x_812;
}
}
}
}
default: 
{
lean_dec(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_813; uint8_t x_814; lean_object* x_815; 
lean_dec(x_22);
x_813 = lean_ctor_get(x_4, 2);
lean_inc(x_813);
x_814 = 1;
x_815 = l_Lean_Meta_substCore(x_1, x_2, x_814, x_813, x_814, x_7, x_32);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
x_818 = lean_ctor_get(x_816, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_816, 1);
lean_inc(x_819);
lean_dec(x_816);
x_820 = lean_ctor_get(x_4, 1);
lean_inc(x_820);
lean_dec(x_4);
x_821 = x_820;
x_822 = lean_unsigned_to_nat(0u);
x_823 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25(x_818, x_822, x_821);
x_824 = x_823;
x_825 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_825, 0, x_819);
lean_ctor_set(x_825, 1, x_824);
lean_ctor_set(x_825, 2, x_818);
x_826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_826, 0, x_825);
lean_ctor_set(x_826, 1, x_5);
x_827 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_826, x_7, x_817);
lean_dec(x_7);
return x_827;
}
else
{
uint8_t x_828; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_828 = !lean_is_exclusive(x_815);
if (x_828 == 0)
{
return x_815;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_829 = lean_ctor_get(x_815, 0);
x_830 = lean_ctor_get(x_815, 1);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_815);
x_831 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_831, 0, x_829);
lean_ctor_set(x_831, 1, x_830);
return x_831;
}
}
}
else
{
lean_object* x_832; 
lean_dec(x_22);
x_832 = l_Lean_Meta_injectionCore(x_1, x_2, x_7, x_32);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
if (lean_obj_tag(x_833) == 0)
{
uint8_t x_834; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_834 = !lean_is_exclusive(x_832);
if (x_834 == 0)
{
lean_object* x_835; lean_object* x_836; 
x_835 = lean_ctor_get(x_832, 0);
lean_dec(x_835);
x_836 = lean_box(0);
lean_ctor_set(x_832, 0, x_836);
return x_832;
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_837 = lean_ctor_get(x_832, 1);
lean_inc(x_837);
lean_dec(x_832);
x_838 = lean_box(0);
x_839 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_837);
return x_839;
}
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_840 = lean_ctor_get(x_832, 1);
lean_inc(x_840);
lean_dec(x_832);
x_841 = lean_ctor_get(x_833, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_833, 1);
lean_inc(x_842);
lean_dec(x_833);
x_843 = lean_nat_add(x_3, x_842);
lean_dec(x_842);
x_844 = lean_ctor_get(x_4, 1);
lean_inc(x_844);
x_845 = lean_ctor_get(x_4, 2);
lean_inc(x_845);
lean_dec(x_4);
x_846 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_846, 0, x_841);
lean_ctor_set(x_846, 1, x_844);
lean_ctor_set(x_846, 2, x_845);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_5);
x_848 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_843, x_847, x_7, x_840);
lean_dec(x_7);
lean_dec(x_843);
return x_848;
}
}
else
{
uint8_t x_849; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_849 = !lean_is_exclusive(x_832);
if (x_849 == 0)
{
return x_832;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_850 = lean_ctor_get(x_832, 0);
x_851 = lean_ctor_get(x_832, 1);
lean_inc(x_851);
lean_inc(x_850);
lean_dec(x_832);
x_852 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_852, 0, x_850);
lean_ctor_set(x_852, 1, x_851);
return x_852;
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
uint8_t x_853; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_853 = !lean_is_exclusive(x_30);
if (x_853 == 0)
{
return x_30;
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_854 = lean_ctor_get(x_30, 0);
x_855 = lean_ctor_get(x_30, 1);
lean_inc(x_855);
lean_inc(x_854);
lean_dec(x_30);
x_856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
return x_856;
}
}
}
else
{
uint8_t x_857; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_857 = !lean_is_exclusive(x_27);
if (x_857 == 0)
{
return x_27;
}
else
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_858 = lean_ctor_get(x_27, 0);
x_859 = lean_ctor_get(x_27, 1);
lean_inc(x_859);
lean_inc(x_858);
lean_dec(x_27);
x_860 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_860, 0, x_858);
lean_ctor_set(x_860, 1, x_859);
return x_860;
}
}
}
else
{
lean_object* x_861; lean_object* x_862; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
x_861 = lean_ctor_get(x_23, 1);
lean_inc(x_861);
lean_dec(x_23);
x_862 = l_Lean_Meta_clear(x_1, x_2, x_7, x_861);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
lean_dec(x_862);
x_865 = lean_ctor_get(x_4, 1);
lean_inc(x_865);
x_866 = lean_ctor_get(x_4, 2);
lean_inc(x_866);
lean_dec(x_4);
x_867 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_867, 0, x_863);
lean_ctor_set(x_867, 1, x_865);
lean_ctor_set(x_867, 2, x_866);
x_868 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_5);
x_869 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_868, x_7, x_864);
lean_dec(x_7);
return x_869;
}
else
{
uint8_t x_870; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_870 = !lean_is_exclusive(x_862);
if (x_870 == 0)
{
return x_862;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_871 = lean_ctor_get(x_862, 0);
x_872 = lean_ctor_get(x_862, 1);
lean_inc(x_872);
lean_inc(x_871);
lean_dec(x_862);
x_873 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_873, 0, x_871);
lean_ctor_set(x_873, 1, x_872);
return x_873;
}
}
}
}
else
{
uint8_t x_874; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_874 = !lean_is_exclusive(x_23);
if (x_874 == 0)
{
return x_23;
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_875 = lean_ctor_get(x_23, 0);
x_876 = lean_ctor_get(x_23, 1);
lean_inc(x_876);
lean_inc(x_875);
lean_dec(x_23);
x_877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_877, 0, x_875);
lean_ctor_set(x_877, 1, x_876);
return x_877;
}
}
}
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_878 = l_Lean_Expr_appFn_x21(x_9);
x_879 = l_Lean_Expr_appFn_x21(x_878);
lean_dec(x_878);
x_880 = l_Lean_Expr_appArg_x21(x_879);
lean_dec(x_879);
x_881 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_2);
x_882 = l_Lean_mkFVar(x_2);
lean_inc(x_7);
x_883 = l_Lean_Meta_mkEqOfHEq(x_882, x_7, x_8);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
lean_inc(x_7);
x_886 = l_Lean_Meta_mkEq(x_880, x_881, x_7, x_885);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
lean_dec(x_886);
x_889 = l_Lean_LocalDecl_userName(x_6);
x_890 = l_Lean_Meta_assert(x_1, x_889, x_887, x_884, x_7, x_888);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
x_893 = l_Lean_Meta_clear(x_891, x_2, x_7, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
x_896 = lean_unsigned_to_nat(1u);
x_897 = lean_nat_add(x_3, x_896);
x_898 = lean_ctor_get(x_4, 1);
lean_inc(x_898);
x_899 = lean_ctor_get(x_4, 2);
lean_inc(x_899);
lean_dec(x_4);
x_900 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_900, 0, x_894);
lean_ctor_set(x_900, 1, x_898);
lean_ctor_set(x_900, 2, x_899);
x_901 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_901, 0, x_900);
lean_ctor_set(x_901, 1, x_5);
x_902 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_897, x_901, x_7, x_895);
lean_dec(x_7);
lean_dec(x_897);
return x_902;
}
else
{
uint8_t x_903; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_903 = !lean_is_exclusive(x_893);
if (x_903 == 0)
{
return x_893;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_904 = lean_ctor_get(x_893, 0);
x_905 = lean_ctor_get(x_893, 1);
lean_inc(x_905);
lean_inc(x_904);
lean_dec(x_893);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_905);
return x_906;
}
}
}
else
{
uint8_t x_907; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_907 = !lean_is_exclusive(x_890);
if (x_907 == 0)
{
return x_890;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_908 = lean_ctor_get(x_890, 0);
x_909 = lean_ctor_get(x_890, 1);
lean_inc(x_909);
lean_inc(x_908);
lean_dec(x_890);
x_910 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_910, 0, x_908);
lean_ctor_set(x_910, 1, x_909);
return x_910;
}
}
}
else
{
uint8_t x_911; 
lean_dec(x_884);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_911 = !lean_is_exclusive(x_886);
if (x_911 == 0)
{
return x_886;
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_912 = lean_ctor_get(x_886, 0);
x_913 = lean_ctor_get(x_886, 1);
lean_inc(x_913);
lean_inc(x_912);
lean_dec(x_886);
x_914 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_914, 0, x_912);
lean_ctor_set(x_914, 1, x_913);
return x_914;
}
}
}
else
{
uint8_t x_915; 
lean_dec(x_881);
lean_dec(x_880);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_915 = !lean_is_exclusive(x_883);
if (x_915 == 0)
{
return x_883;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_883, 0);
x_917 = lean_ctor_get(x_883, 1);
lean_inc(x_917);
lean_inc(x_916);
lean_dec(x_883);
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
return x_918;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs [");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_39 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
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
x_49 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__4;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__7;
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
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___boxed), 8, 5);
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
x_61 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
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
x_73 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__10;
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_1, x_11, x_6, x_7);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_empty___closed__1;
x_7 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l_Lean_Meta_getInductiveUniverseAndParams(x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_casesOnSuffix;
x_18 = lean_name_mk_string(x_16, x_17);
x_19 = lean_ctor_get(x_14, 4);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_List_redLength___main___rarg(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
x_22 = l_List_toArrayAux___main___rarg(x_19, x_21);
lean_inc(x_3);
x_23 = l_Lean_Meta_induction(x_2, x_3, x_18, x_4, x_5, x_7, x_11);
lean_dec(x_7);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(x_25, x_22, x_3, x_12, x_13);
lean_dec(x_13);
lean_dec(x_22);
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
x_29 = l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(x_27, x_22, x_3, x_12, x_13);
lean_dec(x_13);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
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
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
return x_9;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_8 = l_Lean_mkFVar(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_inferType), 3, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(x_4);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1___boxed), 8, 5);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 4);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_withLocalContext___rarg(x_16, x_17, x_12, x_6, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_6);
return x_9;
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
x_10 = l___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f(x_3, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Cases_cases___lambda__1___closed__3;
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_13, x_14, x_6, x_12);
lean_dec(x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Meta_generalizeIndices(x_1, x_3, x_6, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_68; uint8_t x_69; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
x_68 = lean_ctor_get(x_24, 4);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_68, sizeof(void*)*1);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = 0;
x_27 = x_70;
x_28 = x_24;
goto block_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
x_72 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_71, x_6, x_24);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_27 = x_75;
x_28 = x_74;
goto block_67;
}
block_67:
{
if (x_27 == 0)
{
lean_object* x_29; 
x_29 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(x_25, x_26, x_4, x_5, x_17, x_6, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_23);
x_32 = l___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices(x_23, x_30, x_6, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_23, 3);
lean_inc(x_35);
lean_dec(x_23);
x_36 = l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(x_35, x_33, x_6, x_34);
lean_dec(x_6);
lean_dec(x_33);
lean_dec(x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
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
lean_dec(x_23);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_25);
x_45 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_45, 0, x_25);
x_46 = l_Lean_Meta_Cases_cases___lambda__1___closed__7;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
x_49 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_48, x_47, x_6, x_28);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(x_25, x_26, x_4, x_5, x_17, x_6, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_6);
lean_inc(x_23);
x_54 = l___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices(x_23, x_52, x_6, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_23, 3);
lean_inc(x_57);
lean_dec(x_23);
x_58 = l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(x_57, x_55, x_6, x_56);
lean_dec(x_6);
lean_dec(x_55);
lean_dec(x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_23);
lean_dec(x_6);
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
lean_dec(x_23);
lean_dec(x_6);
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
return x_51;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
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
lean_object* x_80; 
x_80 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(x_1, x_3, x_4, x_5, x_17, x_6, x_16);
lean_dec(x_6);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_10);
if (x_81 == 0)
{
return x_10;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_10, 0);
x_83 = lean_ctor_get(x_10, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_10);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_8);
if (x_85 == 0)
{
return x_8;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_8, 0);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_8);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_12__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
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
l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__1);
l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__2);
l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3);
l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__1);
l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2);
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
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__2);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__3);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__4);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__5 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__5);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__6 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__6);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__7 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__7);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__8 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__8);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__9 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__9);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__10 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__10);
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
res = l___private_Lean_Meta_Tactic_Cases_12__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
