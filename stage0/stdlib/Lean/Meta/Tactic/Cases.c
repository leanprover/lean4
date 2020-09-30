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
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__5;
lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__5;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__3;
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1;
extern lean_object* l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_6__visit_x3f(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__4;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1;
extern lean_object* l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5;
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__2;
lean_object* l_List_redLength___main___rarg(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__1;
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2;
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__3;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__2;
lean_object* l_Lean_Meta_Cases_cases___lambda__1___closed__4;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__2;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__2___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeIndices___lambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3;
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__32(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_12__regTraceClasses(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__38(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_8__dep___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_indentExpr(x_1);
x_8 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_7 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_4__getLevelImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_getAppFn___main(x_8);
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
x_19 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_16);
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
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_8, x_22);
x_24 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l___private_Lean_Expr_3__getAppArgsAux___main(x_8, x_25, x_27);
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
x_32 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_16);
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
x_37 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_34);
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
x_41 = l_Lean_Expr_getAppNumArgsAux___main(x_8, x_40);
x_42 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_41);
x_43 = lean_mk_array(x_41, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_41, x_44);
lean_dec(x_41);
x_46 = l___private_Lean_Expr_3__getAppArgsAux___main(x_8, x_43, x_45);
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
x_51 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_34);
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
x_52 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg(x_8, x_2, x_3, x_4, x_5, x_9);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_11 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_2, x_3, x_4, x_5, x_6, x_10);
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
x_14 = l___private_Lean_Meta_InferType_4__getLevelImp(x_9, x_3, x_4, x_5, x_6, x_13);
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
x_27 = l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
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
x_37 = l___private_Lean_Meta_AppBuilder_6__mkHEqReflImp___closed__1;
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
x_49 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
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
x_59 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp___closed__2;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = lean_array_push(x_2, x_8);
x_17 = lean_array_push(x_3, x_4);
x_18 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l_Lean_Expr_Inhabited;
x_16 = lean_array_get(x_15, x_1, x_4);
x_17 = lean_array_get(x_15, x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(x_16, x_17, x_7, x_8, x_9, x_10, x_11);
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
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1___boxed), 13, 7);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_6);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_1);
lean_closure_set(x_23, 5, x_2);
lean_closure_set(x_23, 6, x_3);
x_24 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2;
x_25 = 0;
x_26 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main___spec__1___rarg(x_24, x_25, x_21, x_23, x_7, x_8, x_9, x_10, x_20);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg(x_1, x_2, x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_23 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_16, x_18, x_11, x_12, x_13, x_14, x_22);
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
x_28 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_27, x_24, x_11, x_12, x_13, x_14, x_25);
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
x_31 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_4, x_29, x_11, x_12, x_13, x_14, x_30);
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
x_36 = l_Lean_Meta_mkFreshExprMVarAt___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__2(x_5, x_6, x_32, x_34, x_21, x_35, x_11, x_12, x_13, x_14, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_37);
x_39 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_7, x_7, x_35, x_37);
x_40 = l_Lean_mkApp(x_39, x_8);
x_41 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_9, x_9, x_35, x_40);
x_42 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_2, x_41, x_11, x_12, x_13, x_14, x_38);
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_16 = l___private_Lean_Meta_Tactic_Cases_2__mkEqAndProof(x_15, x_2, x_10, x_11, x_12, x_13, x_14);
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
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed), 15, 9);
lean_closure_set(x_22, 0, x_8);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_5);
lean_closure_set(x_22, 5, x_6);
lean_closure_set(x_22, 6, x_7);
lean_closure_set(x_22, 7, x_15);
lean_closure_set(x_22, 8, x_21);
x_23 = l___private_Lean_Meta_Tactic_Cases_3__withNewIndexEqsAux___main___rarg___closed__2;
x_24 = 0;
x_25 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main___spec__1___rarg(x_23, x_24, x_19, x_22, x_10, x_11, x_12, x_13, x_18);
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed), 14, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_7);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
x_14 = l___private_Lean_Meta_Tactic_Cases_4__withNewIndexEqs___rarg(x_6, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_7, x_7, x_14, x_1);
x_16 = l_Lean_LocalDecl_userName(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__3), 12, 6);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_7);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_5);
lean_closure_set(x_17, 5, x_6);
x_18 = 0;
x_19 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main___spec__1___rarg(x_16, x_18, x_15, x_17, x_9, x_10, x_11, x_12, x_13);
return x_19;
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_20 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
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
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_28 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__3;
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_52; uint8_t x_53; 
x_35 = lean_array_get_size(x_7);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_52 = lean_nat_add(x_25, x_36);
x_53 = lean_nat_dec_eq(x_35, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_54 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___closed__6;
x_55 = lean_box(0);
x_56 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_54, x_55, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_dec(x_4);
x_37 = x_17;
goto block_51;
}
block_51:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_nat_sub(x_35, x_25);
lean_dec(x_25);
x_39 = l_Array_extract___rarg(x_7, x_38, x_35);
lean_dec(x_35);
x_40 = l_Array_extract___rarg(x_7, x_26, x_36);
lean_dec(x_36);
lean_dec(x_7);
x_41 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_40, x_40, x_26, x_6);
lean_dec(x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
x_42 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_41, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed), 13, 6);
lean_closure_set(x_45, 0, x_41);
lean_closure_set(x_45, 1, x_5);
lean_closure_set(x_45, 2, x_1);
lean_closure_set(x_45, 3, x_2);
lean_closure_set(x_45, 4, x_3);
lean_closure_set(x_45, 5, x_39);
x_46 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_43, x_45, x_9, x_10, x_11, x_12, x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_61 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_62 = lean_box(0);
x_63 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_61, x_62, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_63;
}
}
}
case 5:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_6, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
lean_dec(x_6);
x_66 = lean_array_set(x_7, x_8, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_8, x_67);
lean_dec(x_8);
x_6 = x_64;
x_7 = x_66;
x_8 = x_68;
goto _start;
}
default: 
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_70 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__8;
x_71 = lean_box(0);
x_72 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_1, x_70, x_71, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_72;
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
lean_object* l_Lean_Meta_generalizeIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_getLocalInstances___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_4, x_5, x_6, x_7, x_8);
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
x_19 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_18, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_20, x_22);
x_24 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1(x_1, x_3, x_10, x_12, x_16, x_20, x_25, x_27, x_4, x_5, x_6, x_7, x_21);
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
x_9 = l___private_Lean_Meta_Basic_5__mkFreshExprMVarWithIdCore___rarg___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_7);
return x_16;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_generalizeIndices___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_37 = l_List_lengthAux___main___rarg(x_35, x_36);
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
x_46 = l_List_lengthAux___main___rarg(x_44, x_45);
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
x_80 = l_List_lengthAux___main___rarg(x_78, x_79);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_22 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_21, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux___main(x_23, x_25);
x_27 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
x_31 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(x_11, x_19, x_23, x_28, x_30, x_2, x_3, x_4, x_5, x_24);
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
x_55 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_54, x_2, x_3, x_4, x_5, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lean_Expr_getAppNumArgsAux___main(x_56, x_58);
x_60 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_59);
x_61 = lean_mk_array(x_59, x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_59, x_62);
lean_dec(x_59);
x_64 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(x_42, x_52, x_56, x_61, x_63, x_2, x_3, x_4, x_5, x_57);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__1(x_1, x_7, x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_inc(x_9);
x_12 = l_Nat_anyAux___main___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__3(x_7, x_9, x_9);
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
x_19 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42(x_1, x_7, x_9, x_17, x_18);
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
x_28 = l_Std_PersistentArray_anyM___at___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___spec__42(x_1, x_7, x_9, x_26, x_27);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Cases_6__hasIndepIndices(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_38 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_13, x_21);
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
x_42 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_13, x_21);
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
x_48 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_31, x_5, x_6, x_7, x_8, x_47);
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
x_69 = l_Std_AssocList_erase___main___at_Lean_Meta_FVarSubst_erase___spec__1(x_13, x_54);
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
x_76 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_64, x_5, x_6, x_7, x_8, x_75);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_18 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(x_1, x_2, x_15, x_17, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = x_2;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2___boxed), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_9);
x_12 = x_11;
x_13 = lean_apply_5(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
x_1 = lean_mk_string("unifyEqs [");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = l_Nat_repr(x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__3;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__6;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cases");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_LocalDecl_type(x_7);
x_14 = l_Lean_Expr_heq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Expr_isAppOfArity___main(x_13, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_Expr_eq_x3f___closed__2;
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity___main(x_13, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_24__mkNoConfusionImp___closed__5;
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
x_31 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_25, x_8, x_9, x_10, x_11, x_30);
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
x_34 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_26, x_8, x_9, x_10, x_11, x_33);
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
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_2);
x_38 = l_Lean_mkFVar(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_32, x_35, x_8, x_9, x_10, x_11, x_36);
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
x_53 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_50, x_52, x_8, x_9, x_10, x_11, x_48);
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
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_2);
x_67 = l_Lean_mkFVar(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_32, x_35, x_8, x_9, x_10, x_11, x_36);
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
x_82 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_79, x_81, x_8, x_9, x_10, x_11, x_77);
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
lean_dec(x_28);
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
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
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
x_101 = x_4;
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__1(x_99, x_102, x_101);
x_104 = x_103;
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_99);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_6);
x_107 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_106, x_8, x_9, x_10, x_11, x_98);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_108 = !lean_is_exclusive(x_96);
if (x_108 == 0)
{
return x_96;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_96, 0);
x_110 = lean_ctor_get(x_96, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_96);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_112 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
x_116 = lean_box(0);
lean_ctor_set(x_112, 0, x_116);
return x_112;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
lean_dec(x_112);
x_121 = lean_ctor_get(x_113, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_113, 1);
lean_inc(x_122);
lean_dec(x_113);
x_123 = lean_nat_add(x_3, x_122);
lean_dec(x_122);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_4);
lean_ctor_set(x_124, 2, x_5);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_6);
x_126 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_123, x_125, x_8, x_9, x_10, x_11, x_120);
lean_dec(x_123);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_112);
if (x_127 == 0)
{
return x_112;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_112, 0);
x_129 = lean_ctor_get(x_112, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_112);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
case 1:
{
switch (lean_obj_tag(x_26)) {
case 0:
{
uint8_t x_131; uint8_t x_132; lean_object* x_133; 
lean_dec(x_26);
lean_dec(x_25);
x_131 = 1;
x_132 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_133 = l_Lean_Meta_substCore(x_1, x_2, x_132, x_5, x_131, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = x_4;
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__2(x_136, x_139, x_138);
x_141 = x_140;
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_136);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_6);
x_144 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_143, x_8, x_9, x_10, x_11, x_135);
return x_144;
}
else
{
uint8_t x_145; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_145 = !lean_is_exclusive(x_133);
if (x_145 == 0)
{
return x_133;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_133, 0);
x_147 = lean_ctor_get(x_133, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_133);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
case 1:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_28);
x_149 = lean_ctor_get(x_25, 0);
lean_inc(x_149);
lean_dec(x_25);
x_150 = lean_ctor_get(x_26, 0);
lean_inc(x_150);
lean_dec(x_26);
lean_inc(x_8);
x_151 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_149, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_8);
x_154 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_150, x_8, x_9, x_10, x_11, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_LocalDecl_index(x_152);
lean_dec(x_152);
x_158 = l_Lean_LocalDecl_index(x_155);
lean_dec(x_155);
x_159 = lean_nat_dec_lt(x_157, x_158);
lean_dec(x_158);
lean_dec(x_157);
x_160 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_161 = l_Lean_Meta_substCore(x_1, x_2, x_159, x_5, x_160, x_8, x_9, x_10, x_11, x_156);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = x_4;
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__3(x_164, x_167, x_166);
x_169 = x_168;
x_170 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_164);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_6);
x_172 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_171, x_8, x_9, x_10, x_11, x_163);
return x_172;
}
else
{
uint8_t x_173; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_173 = !lean_is_exclusive(x_161);
if (x_173 == 0)
{
return x_161;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_161, 0);
x_175 = lean_ctor_get(x_161, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_161);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_152);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_154);
if (x_177 == 0)
{
return x_154;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_154, 0);
x_179 = lean_ctor_get(x_154, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_154);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_150);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_151);
if (x_181 == 0)
{
return x_151;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_151, 0);
x_183 = lean_ctor_get(x_151, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_151);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
case 2:
{
uint8_t x_185; uint8_t x_186; lean_object* x_187; 
lean_dec(x_26);
lean_dec(x_25);
x_185 = 1;
x_186 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_187 = l_Lean_Meta_substCore(x_1, x_2, x_186, x_5, x_185, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = x_4;
x_193 = lean_unsigned_to_nat(0u);
x_194 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__4(x_190, x_193, x_192);
x_195 = x_194;
x_196 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_196, 2, x_190);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_6);
x_198 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_197, x_8, x_9, x_10, x_11, x_189);
return x_198;
}
else
{
uint8_t x_199; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_199 = !lean_is_exclusive(x_187);
if (x_199 == 0)
{
return x_187;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_187, 0);
x_201 = lean_ctor_get(x_187, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_187);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
case 3:
{
uint8_t x_203; uint8_t x_204; lean_object* x_205; 
lean_dec(x_26);
lean_dec(x_25);
x_203 = 1;
x_204 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_205 = l_Lean_Meta_substCore(x_1, x_2, x_204, x_5, x_203, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = x_4;
x_211 = lean_unsigned_to_nat(0u);
x_212 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__5(x_208, x_211, x_210);
x_213 = x_212;
x_214 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_214, 0, x_209);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_214, 2, x_208);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_6);
x_216 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_215, x_8, x_9, x_10, x_11, x_207);
return x_216;
}
else
{
uint8_t x_217; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_217 = !lean_is_exclusive(x_205);
if (x_217 == 0)
{
return x_205;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_205, 0);
x_219 = lean_ctor_get(x_205, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_205);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
case 4:
{
uint8_t x_221; uint8_t x_222; lean_object* x_223; 
lean_dec(x_26);
lean_dec(x_25);
x_221 = 1;
x_222 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_223 = l_Lean_Meta_substCore(x_1, x_2, x_222, x_5, x_221, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = x_4;
x_229 = lean_unsigned_to_nat(0u);
x_230 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__6(x_226, x_229, x_228);
x_231 = x_230;
x_232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_232, 0, x_227);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_226);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_6);
x_234 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_233, x_8, x_9, x_10, x_11, x_225);
return x_234;
}
else
{
uint8_t x_235; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_235 = !lean_is_exclusive(x_223);
if (x_235 == 0)
{
return x_223;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_223, 0);
x_237 = lean_ctor_get(x_223, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_223);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
case 5:
{
uint8_t x_239; uint8_t x_240; lean_object* x_241; 
lean_dec(x_26);
lean_dec(x_25);
x_239 = 1;
x_240 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_241 = l_Lean_Meta_substCore(x_1, x_2, x_240, x_5, x_239, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = x_4;
x_247 = lean_unsigned_to_nat(0u);
x_248 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__7(x_244, x_247, x_246);
x_249 = x_248;
x_250 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_250, 0, x_245);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_244);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_6);
x_252 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_251, x_8, x_9, x_10, x_11, x_243);
return x_252;
}
else
{
uint8_t x_253; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_253 = !lean_is_exclusive(x_241);
if (x_253 == 0)
{
return x_241;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_241, 0);
x_255 = lean_ctor_get(x_241, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_241);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
case 6:
{
uint8_t x_257; uint8_t x_258; lean_object* x_259; 
lean_dec(x_26);
lean_dec(x_25);
x_257 = 1;
x_258 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_259 = l_Lean_Meta_substCore(x_1, x_2, x_258, x_5, x_257, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_264 = x_4;
x_265 = lean_unsigned_to_nat(0u);
x_266 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__8(x_262, x_265, x_264);
x_267 = x_266;
x_268 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_268, 0, x_263);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_268, 2, x_262);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_6);
x_270 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_269, x_8, x_9, x_10, x_11, x_261);
return x_270;
}
else
{
uint8_t x_271; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_271 = !lean_is_exclusive(x_259);
if (x_271 == 0)
{
return x_259;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_259, 0);
x_273 = lean_ctor_get(x_259, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_259);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
case 7:
{
uint8_t x_275; uint8_t x_276; lean_object* x_277; 
lean_dec(x_26);
lean_dec(x_25);
x_275 = 1;
x_276 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_277 = l_Lean_Meta_substCore(x_1, x_2, x_276, x_5, x_275, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
lean_dec(x_278);
x_282 = x_4;
x_283 = lean_unsigned_to_nat(0u);
x_284 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__9(x_280, x_283, x_282);
x_285 = x_284;
x_286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_285);
lean_ctor_set(x_286, 2, x_280);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_6);
x_288 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_287, x_8, x_9, x_10, x_11, x_279);
return x_288;
}
else
{
uint8_t x_289; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_289 = !lean_is_exclusive(x_277);
if (x_289 == 0)
{
return x_277;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_277, 0);
x_291 = lean_ctor_get(x_277, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_277);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
case 8:
{
uint8_t x_293; uint8_t x_294; lean_object* x_295; 
lean_dec(x_26);
lean_dec(x_25);
x_293 = 1;
x_294 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_295 = l_Lean_Meta_substCore(x_1, x_2, x_294, x_5, x_293, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
lean_dec(x_296);
x_300 = x_4;
x_301 = lean_unsigned_to_nat(0u);
x_302 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__10(x_298, x_301, x_300);
x_303 = x_302;
x_304 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_304, 0, x_299);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_304, 2, x_298);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_6);
x_306 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_305, x_8, x_9, x_10, x_11, x_297);
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
x_307 = !lean_is_exclusive(x_295);
if (x_307 == 0)
{
return x_295;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_295, 0);
x_309 = lean_ctor_get(x_295, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_295);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
case 9:
{
uint8_t x_311; uint8_t x_312; lean_object* x_313; 
lean_dec(x_26);
lean_dec(x_25);
x_311 = 1;
x_312 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_313 = l_Lean_Meta_substCore(x_1, x_2, x_312, x_5, x_311, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
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
x_318 = x_4;
x_319 = lean_unsigned_to_nat(0u);
x_320 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__11(x_316, x_319, x_318);
x_321 = x_320;
x_322 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set(x_322, 1, x_321);
lean_ctor_set(x_322, 2, x_316);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_6);
x_324 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_323, x_8, x_9, x_10, x_11, x_315);
return x_324;
}
else
{
uint8_t x_325; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_325 = !lean_is_exclusive(x_313);
if (x_325 == 0)
{
return x_313;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_313, 0);
x_327 = lean_ctor_get(x_313, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_313);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
case 10:
{
uint8_t x_329; uint8_t x_330; lean_object* x_331; 
lean_dec(x_26);
lean_dec(x_25);
x_329 = 1;
x_330 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_331 = l_Lean_Meta_substCore(x_1, x_2, x_330, x_5, x_329, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec(x_332);
x_336 = x_4;
x_337 = lean_unsigned_to_nat(0u);
x_338 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__12(x_334, x_337, x_336);
x_339 = x_338;
x_340 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_340, 0, x_335);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set(x_340, 2, x_334);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_6);
x_342 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_341, x_8, x_9, x_10, x_11, x_333);
return x_342;
}
else
{
uint8_t x_343; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_343 = !lean_is_exclusive(x_331);
if (x_343 == 0)
{
return x_331;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_331, 0);
x_345 = lean_ctor_get(x_331, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_331);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
case 11:
{
uint8_t x_347; uint8_t x_348; lean_object* x_349; 
lean_dec(x_26);
lean_dec(x_25);
x_347 = 1;
x_348 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_349 = l_Lean_Meta_substCore(x_1, x_2, x_348, x_5, x_347, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get(x_350, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_350, 1);
lean_inc(x_353);
lean_dec(x_350);
x_354 = x_4;
x_355 = lean_unsigned_to_nat(0u);
x_356 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__13(x_352, x_355, x_354);
x_357 = x_356;
x_358 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set(x_358, 2, x_352);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_6);
x_360 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_359, x_8, x_9, x_10, x_11, x_351);
return x_360;
}
else
{
uint8_t x_361; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_361 = !lean_is_exclusive(x_349);
if (x_361 == 0)
{
return x_349;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_349, 0);
x_363 = lean_ctor_get(x_349, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_349);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
default: 
{
uint8_t x_365; uint8_t x_366; lean_object* x_367; 
lean_dec(x_26);
lean_dec(x_25);
x_365 = 1;
x_366 = lean_unbox(x_28);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_367 = l_Lean_Meta_substCore(x_1, x_2, x_366, x_5, x_365, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_dec(x_368);
x_372 = x_4;
x_373 = lean_unsigned_to_nat(0u);
x_374 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__14(x_370, x_373, x_372);
x_375 = x_374;
x_376 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_376, 0, x_371);
lean_ctor_set(x_376, 1, x_375);
lean_ctor_set(x_376, 2, x_370);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_6);
x_378 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_377, x_8, x_9, x_10, x_11, x_369);
return x_378;
}
else
{
uint8_t x_379; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_379 = !lean_is_exclusive(x_367);
if (x_379 == 0)
{
return x_367;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_367, 0);
x_381 = lean_ctor_get(x_367, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_367);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
}
}
case 2:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_383; lean_object* x_384; 
lean_dec(x_26);
x_383 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_384 = l_Lean_Meta_substCore(x_1, x_2, x_383, x_5, x_383, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_ctor_get(x_385, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_dec(x_385);
x_389 = x_4;
x_390 = lean_unsigned_to_nat(0u);
x_391 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__15(x_387, x_390, x_389);
x_392 = x_391;
x_393 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_393, 0, x_388);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set(x_393, 2, x_387);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_6);
x_395 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_394, x_8, x_9, x_10, x_11, x_386);
return x_395;
}
else
{
uint8_t x_396; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_396 = !lean_is_exclusive(x_384);
if (x_396 == 0)
{
return x_384;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_384, 0);
x_398 = lean_ctor_get(x_384, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_384);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
lean_object* x_400; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_400 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
if (lean_obj_tag(x_401) == 0)
{
uint8_t x_402; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_402 = !lean_is_exclusive(x_400);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_400, 0);
lean_dec(x_403);
x_404 = lean_box(0);
lean_ctor_set(x_400, 0, x_404);
return x_400;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_400, 1);
lean_inc(x_405);
lean_dec(x_400);
x_406 = lean_box(0);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_408 = lean_ctor_get(x_400, 1);
lean_inc(x_408);
lean_dec(x_400);
x_409 = lean_ctor_get(x_401, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_401, 1);
lean_inc(x_410);
lean_dec(x_401);
x_411 = lean_nat_add(x_3, x_410);
lean_dec(x_410);
x_412 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_4);
lean_ctor_set(x_412, 2, x_5);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_6);
x_414 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_411, x_413, x_8, x_9, x_10, x_11, x_408);
lean_dec(x_411);
return x_414;
}
}
else
{
uint8_t x_415; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_415 = !lean_is_exclusive(x_400);
if (x_415 == 0)
{
return x_400;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_400, 0);
x_417 = lean_ctor_get(x_400, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_400);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
}
case 3:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_419; lean_object* x_420; 
lean_dec(x_26);
x_419 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_420 = l_Lean_Meta_substCore(x_1, x_2, x_419, x_5, x_419, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_ctor_get(x_421, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_421, 1);
lean_inc(x_424);
lean_dec(x_421);
x_425 = x_4;
x_426 = lean_unsigned_to_nat(0u);
x_427 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__16(x_423, x_426, x_425);
x_428 = x_427;
x_429 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_429, 0, x_424);
lean_ctor_set(x_429, 1, x_428);
lean_ctor_set(x_429, 2, x_423);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_6);
x_431 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_430, x_8, x_9, x_10, x_11, x_422);
return x_431;
}
else
{
uint8_t x_432; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_432 = !lean_is_exclusive(x_420);
if (x_432 == 0)
{
return x_420;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_420, 0);
x_434 = lean_ctor_get(x_420, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_420);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
}
else
{
lean_object* x_436; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_436 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
if (lean_obj_tag(x_437) == 0)
{
uint8_t x_438; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_438 = !lean_is_exclusive(x_436);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_436, 0);
lean_dec(x_439);
x_440 = lean_box(0);
lean_ctor_set(x_436, 0, x_440);
return x_436;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_436, 1);
lean_inc(x_441);
lean_dec(x_436);
x_442 = lean_box(0);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_444 = lean_ctor_get(x_436, 1);
lean_inc(x_444);
lean_dec(x_436);
x_445 = lean_ctor_get(x_437, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_437, 1);
lean_inc(x_446);
lean_dec(x_437);
x_447 = lean_nat_add(x_3, x_446);
lean_dec(x_446);
x_448 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_4);
lean_ctor_set(x_448, 2, x_5);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_6);
x_450 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_447, x_449, x_8, x_9, x_10, x_11, x_444);
lean_dec(x_447);
return x_450;
}
}
else
{
uint8_t x_451; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_451 = !lean_is_exclusive(x_436);
if (x_451 == 0)
{
return x_436;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_436, 0);
x_453 = lean_ctor_get(x_436, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_436);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
}
case 4:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_455; lean_object* x_456; 
lean_dec(x_26);
x_455 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_456 = l_Lean_Meta_substCore(x_1, x_2, x_455, x_5, x_455, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
lean_dec(x_457);
x_461 = x_4;
x_462 = lean_unsigned_to_nat(0u);
x_463 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__17(x_459, x_462, x_461);
x_464 = x_463;
x_465 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_465, 0, x_460);
lean_ctor_set(x_465, 1, x_464);
lean_ctor_set(x_465, 2, x_459);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_6);
x_467 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_466, x_8, x_9, x_10, x_11, x_458);
return x_467;
}
else
{
uint8_t x_468; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_468 = !lean_is_exclusive(x_456);
if (x_468 == 0)
{
return x_456;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_456, 0);
x_470 = lean_ctor_get(x_456, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_456);
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
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_472 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
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
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
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
x_484 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_4);
lean_ctor_set(x_484, 2, x_5);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_6);
x_486 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_483, x_485, x_8, x_9, x_10, x_11, x_480);
lean_dec(x_483);
return x_486;
}
}
else
{
uint8_t x_487; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_487 = !lean_is_exclusive(x_472);
if (x_487 == 0)
{
return x_472;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_472, 0);
x_489 = lean_ctor_get(x_472, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_472);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
}
case 5:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_491; lean_object* x_492; 
lean_dec(x_26);
x_491 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_492 = l_Lean_Meta_substCore(x_1, x_2, x_491, x_5, x_491, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
x_495 = lean_ctor_get(x_493, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_493, 1);
lean_inc(x_496);
lean_dec(x_493);
x_497 = x_4;
x_498 = lean_unsigned_to_nat(0u);
x_499 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__18(x_495, x_498, x_497);
x_500 = x_499;
x_501 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_501, 0, x_496);
lean_ctor_set(x_501, 1, x_500);
lean_ctor_set(x_501, 2, x_495);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_6);
x_503 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_502, x_8, x_9, x_10, x_11, x_494);
return x_503;
}
else
{
uint8_t x_504; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_504 = !lean_is_exclusive(x_492);
if (x_504 == 0)
{
return x_492;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_ctor_get(x_492, 0);
x_506 = lean_ctor_get(x_492, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_492);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
return x_507;
}
}
}
else
{
lean_object* x_508; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_508 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
uint8_t x_510; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_510 = !lean_is_exclusive(x_508);
if (x_510 == 0)
{
lean_object* x_511; lean_object* x_512; 
x_511 = lean_ctor_get(x_508, 0);
lean_dec(x_511);
x_512 = lean_box(0);
lean_ctor_set(x_508, 0, x_512);
return x_508;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_508, 1);
lean_inc(x_513);
lean_dec(x_508);
x_514 = lean_box(0);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_516 = lean_ctor_get(x_508, 1);
lean_inc(x_516);
lean_dec(x_508);
x_517 = lean_ctor_get(x_509, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_509, 1);
lean_inc(x_518);
lean_dec(x_509);
x_519 = lean_nat_add(x_3, x_518);
lean_dec(x_518);
x_520 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_4);
lean_ctor_set(x_520, 2, x_5);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_6);
x_522 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_519, x_521, x_8, x_9, x_10, x_11, x_516);
lean_dec(x_519);
return x_522;
}
}
else
{
uint8_t x_523; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_523 = !lean_is_exclusive(x_508);
if (x_523 == 0)
{
return x_508;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_508, 0);
x_525 = lean_ctor_get(x_508, 1);
lean_inc(x_525);
lean_inc(x_524);
lean_dec(x_508);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
}
}
case 6:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_527; lean_object* x_528; 
lean_dec(x_26);
x_527 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_528 = l_Lean_Meta_substCore(x_1, x_2, x_527, x_5, x_527, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
x_531 = lean_ctor_get(x_529, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_532);
lean_dec(x_529);
x_533 = x_4;
x_534 = lean_unsigned_to_nat(0u);
x_535 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__19(x_531, x_534, x_533);
x_536 = x_535;
x_537 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_537, 0, x_532);
lean_ctor_set(x_537, 1, x_536);
lean_ctor_set(x_537, 2, x_531);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_6);
x_539 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_538, x_8, x_9, x_10, x_11, x_530);
return x_539;
}
else
{
uint8_t x_540; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_540 = !lean_is_exclusive(x_528);
if (x_540 == 0)
{
return x_528;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_528, 0);
x_542 = lean_ctor_get(x_528, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_528);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
else
{
lean_object* x_544; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_544 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
if (lean_obj_tag(x_545) == 0)
{
uint8_t x_546; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_546 = !lean_is_exclusive(x_544);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; 
x_547 = lean_ctor_get(x_544, 0);
lean_dec(x_547);
x_548 = lean_box(0);
lean_ctor_set(x_544, 0, x_548);
return x_544;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_544, 1);
lean_inc(x_549);
lean_dec(x_544);
x_550 = lean_box(0);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_552 = lean_ctor_get(x_544, 1);
lean_inc(x_552);
lean_dec(x_544);
x_553 = lean_ctor_get(x_545, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_545, 1);
lean_inc(x_554);
lean_dec(x_545);
x_555 = lean_nat_add(x_3, x_554);
lean_dec(x_554);
x_556 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_556, 0, x_553);
lean_ctor_set(x_556, 1, x_4);
lean_ctor_set(x_556, 2, x_5);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_6);
x_558 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_555, x_557, x_8, x_9, x_10, x_11, x_552);
lean_dec(x_555);
return x_558;
}
}
else
{
uint8_t x_559; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_559 = !lean_is_exclusive(x_544);
if (x_559 == 0)
{
return x_544;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_544, 0);
x_561 = lean_ctor_get(x_544, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_544);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
}
}
case 7:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_563; lean_object* x_564; 
lean_dec(x_26);
x_563 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_564 = l_Lean_Meta_substCore(x_1, x_2, x_563, x_5, x_563, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = lean_ctor_get(x_565, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_565, 1);
lean_inc(x_568);
lean_dec(x_565);
x_569 = x_4;
x_570 = lean_unsigned_to_nat(0u);
x_571 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__20(x_567, x_570, x_569);
x_572 = x_571;
x_573 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_573, 0, x_568);
lean_ctor_set(x_573, 1, x_572);
lean_ctor_set(x_573, 2, x_567);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_6);
x_575 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_574, x_8, x_9, x_10, x_11, x_566);
return x_575;
}
else
{
uint8_t x_576; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_576 = !lean_is_exclusive(x_564);
if (x_576 == 0)
{
return x_564;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_564, 0);
x_578 = lean_ctor_get(x_564, 1);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_564);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
return x_579;
}
}
}
else
{
lean_object* x_580; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_580 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
if (lean_obj_tag(x_581) == 0)
{
uint8_t x_582; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_582 = !lean_is_exclusive(x_580);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; 
x_583 = lean_ctor_get(x_580, 0);
lean_dec(x_583);
x_584 = lean_box(0);
lean_ctor_set(x_580, 0, x_584);
return x_580;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_580, 1);
lean_inc(x_585);
lean_dec(x_580);
x_586 = lean_box(0);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_585);
return x_587;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_588 = lean_ctor_get(x_580, 1);
lean_inc(x_588);
lean_dec(x_580);
x_589 = lean_ctor_get(x_581, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_581, 1);
lean_inc(x_590);
lean_dec(x_581);
x_591 = lean_nat_add(x_3, x_590);
lean_dec(x_590);
x_592 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_592, 0, x_589);
lean_ctor_set(x_592, 1, x_4);
lean_ctor_set(x_592, 2, x_5);
x_593 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_6);
x_594 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_591, x_593, x_8, x_9, x_10, x_11, x_588);
lean_dec(x_591);
return x_594;
}
}
else
{
uint8_t x_595; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_595 = !lean_is_exclusive(x_580);
if (x_595 == 0)
{
return x_580;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_580, 0);
x_597 = lean_ctor_get(x_580, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_580);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
}
case 8:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_599; lean_object* x_600; 
lean_dec(x_26);
x_599 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_600 = l_Lean_Meta_substCore(x_1, x_2, x_599, x_5, x_599, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = lean_ctor_get(x_601, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_601, 1);
lean_inc(x_604);
lean_dec(x_601);
x_605 = x_4;
x_606 = lean_unsigned_to_nat(0u);
x_607 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__21(x_603, x_606, x_605);
x_608 = x_607;
x_609 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_609, 0, x_604);
lean_ctor_set(x_609, 1, x_608);
lean_ctor_set(x_609, 2, x_603);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_6);
x_611 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_610, x_8, x_9, x_10, x_11, x_602);
return x_611;
}
else
{
uint8_t x_612; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_612 = !lean_is_exclusive(x_600);
if (x_612 == 0)
{
return x_600;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_600, 0);
x_614 = lean_ctor_get(x_600, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_600);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
else
{
lean_object* x_616; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_616 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
if (lean_obj_tag(x_617) == 0)
{
uint8_t x_618; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_618 = !lean_is_exclusive(x_616);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; 
x_619 = lean_ctor_get(x_616, 0);
lean_dec(x_619);
x_620 = lean_box(0);
lean_ctor_set(x_616, 0, x_620);
return x_616;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_616, 1);
lean_inc(x_621);
lean_dec(x_616);
x_622 = lean_box(0);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_624 = lean_ctor_get(x_616, 1);
lean_inc(x_624);
lean_dec(x_616);
x_625 = lean_ctor_get(x_617, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_617, 1);
lean_inc(x_626);
lean_dec(x_617);
x_627 = lean_nat_add(x_3, x_626);
lean_dec(x_626);
x_628 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_4);
lean_ctor_set(x_628, 2, x_5);
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_6);
x_630 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_627, x_629, x_8, x_9, x_10, x_11, x_624);
lean_dec(x_627);
return x_630;
}
}
else
{
uint8_t x_631; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_631 = !lean_is_exclusive(x_616);
if (x_631 == 0)
{
return x_616;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_616, 0);
x_633 = lean_ctor_get(x_616, 1);
lean_inc(x_633);
lean_inc(x_632);
lean_dec(x_616);
x_634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
return x_634;
}
}
}
}
case 9:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_635; lean_object* x_636; 
lean_dec(x_26);
x_635 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_636 = l_Lean_Meta_substCore(x_1, x_2, x_635, x_5, x_635, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
lean_dec(x_636);
x_639 = lean_ctor_get(x_637, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_637, 1);
lean_inc(x_640);
lean_dec(x_637);
x_641 = x_4;
x_642 = lean_unsigned_to_nat(0u);
x_643 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__22(x_639, x_642, x_641);
x_644 = x_643;
x_645 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_645, 0, x_640);
lean_ctor_set(x_645, 1, x_644);
lean_ctor_set(x_645, 2, x_639);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_6);
x_647 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_646, x_8, x_9, x_10, x_11, x_638);
return x_647;
}
else
{
uint8_t x_648; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_648 = !lean_is_exclusive(x_636);
if (x_648 == 0)
{
return x_636;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_636, 0);
x_650 = lean_ctor_get(x_636, 1);
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_636);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
return x_651;
}
}
}
else
{
lean_object* x_652; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_652 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
if (lean_obj_tag(x_653) == 0)
{
uint8_t x_654; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_654 = !lean_is_exclusive(x_652);
if (x_654 == 0)
{
lean_object* x_655; lean_object* x_656; 
x_655 = lean_ctor_get(x_652, 0);
lean_dec(x_655);
x_656 = lean_box(0);
lean_ctor_set(x_652, 0, x_656);
return x_652;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_652, 1);
lean_inc(x_657);
lean_dec(x_652);
x_658 = lean_box(0);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_657);
return x_659;
}
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_660 = lean_ctor_get(x_652, 1);
lean_inc(x_660);
lean_dec(x_652);
x_661 = lean_ctor_get(x_653, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_653, 1);
lean_inc(x_662);
lean_dec(x_653);
x_663 = lean_nat_add(x_3, x_662);
lean_dec(x_662);
x_664 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_4);
lean_ctor_set(x_664, 2, x_5);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_6);
x_666 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_663, x_665, x_8, x_9, x_10, x_11, x_660);
lean_dec(x_663);
return x_666;
}
}
else
{
uint8_t x_667; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_667 = !lean_is_exclusive(x_652);
if (x_667 == 0)
{
return x_652;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_668 = lean_ctor_get(x_652, 0);
x_669 = lean_ctor_get(x_652, 1);
lean_inc(x_669);
lean_inc(x_668);
lean_dec(x_652);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_668);
lean_ctor_set(x_670, 1, x_669);
return x_670;
}
}
}
}
case 10:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_671; lean_object* x_672; 
lean_dec(x_26);
x_671 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_672 = l_Lean_Meta_substCore(x_1, x_2, x_671, x_5, x_671, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = lean_ctor_get(x_673, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_673, 1);
lean_inc(x_676);
lean_dec(x_673);
x_677 = x_4;
x_678 = lean_unsigned_to_nat(0u);
x_679 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__23(x_675, x_678, x_677);
x_680 = x_679;
x_681 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_681, 0, x_676);
lean_ctor_set(x_681, 1, x_680);
lean_ctor_set(x_681, 2, x_675);
x_682 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_6);
x_683 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_682, x_8, x_9, x_10, x_11, x_674);
return x_683;
}
else
{
uint8_t x_684; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_684 = !lean_is_exclusive(x_672);
if (x_684 == 0)
{
return x_672;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_672, 0);
x_686 = lean_ctor_get(x_672, 1);
lean_inc(x_686);
lean_inc(x_685);
lean_dec(x_672);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
return x_687;
}
}
}
else
{
lean_object* x_688; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_688 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
if (lean_obj_tag(x_689) == 0)
{
uint8_t x_690; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_690 = !lean_is_exclusive(x_688);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; 
x_691 = lean_ctor_get(x_688, 0);
lean_dec(x_691);
x_692 = lean_box(0);
lean_ctor_set(x_688, 0, x_692);
return x_688;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_688, 1);
lean_inc(x_693);
lean_dec(x_688);
x_694 = lean_box(0);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_693);
return x_695;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_696 = lean_ctor_get(x_688, 1);
lean_inc(x_696);
lean_dec(x_688);
x_697 = lean_ctor_get(x_689, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_689, 1);
lean_inc(x_698);
lean_dec(x_689);
x_699 = lean_nat_add(x_3, x_698);
lean_dec(x_698);
x_700 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_4);
lean_ctor_set(x_700, 2, x_5);
x_701 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_701, 0, x_700);
lean_ctor_set(x_701, 1, x_6);
x_702 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_699, x_701, x_8, x_9, x_10, x_11, x_696);
lean_dec(x_699);
return x_702;
}
}
else
{
uint8_t x_703; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_703 = !lean_is_exclusive(x_688);
if (x_703 == 0)
{
return x_688;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_704 = lean_ctor_get(x_688, 0);
x_705 = lean_ctor_get(x_688, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_688);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
return x_706;
}
}
}
}
case 11:
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_707; lean_object* x_708; 
lean_dec(x_26);
x_707 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_708 = l_Lean_Meta_substCore(x_1, x_2, x_707, x_5, x_707, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
lean_dec(x_708);
x_711 = lean_ctor_get(x_709, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_709, 1);
lean_inc(x_712);
lean_dec(x_709);
x_713 = x_4;
x_714 = lean_unsigned_to_nat(0u);
x_715 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__24(x_711, x_714, x_713);
x_716 = x_715;
x_717 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_717, 0, x_712);
lean_ctor_set(x_717, 1, x_716);
lean_ctor_set(x_717, 2, x_711);
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_6);
x_719 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_718, x_8, x_9, x_10, x_11, x_710);
return x_719;
}
else
{
uint8_t x_720; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_720 = !lean_is_exclusive(x_708);
if (x_720 == 0)
{
return x_708;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_708, 0);
x_722 = lean_ctor_get(x_708, 1);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_708);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
else
{
lean_object* x_724; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_724 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
if (lean_obj_tag(x_725) == 0)
{
uint8_t x_726; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_726 = !lean_is_exclusive(x_724);
if (x_726 == 0)
{
lean_object* x_727; lean_object* x_728; 
x_727 = lean_ctor_get(x_724, 0);
lean_dec(x_727);
x_728 = lean_box(0);
lean_ctor_set(x_724, 0, x_728);
return x_724;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_724, 1);
lean_inc(x_729);
lean_dec(x_724);
x_730 = lean_box(0);
x_731 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_729);
return x_731;
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_732 = lean_ctor_get(x_724, 1);
lean_inc(x_732);
lean_dec(x_724);
x_733 = lean_ctor_get(x_725, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_725, 1);
lean_inc(x_734);
lean_dec(x_725);
x_735 = lean_nat_add(x_3, x_734);
lean_dec(x_734);
x_736 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_4);
lean_ctor_set(x_736, 2, x_5);
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_6);
x_738 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_735, x_737, x_8, x_9, x_10, x_11, x_732);
lean_dec(x_735);
return x_738;
}
}
else
{
uint8_t x_739; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_739 = !lean_is_exclusive(x_724);
if (x_739 == 0)
{
return x_724;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_724, 0);
x_741 = lean_ctor_get(x_724, 1);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_724);
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set(x_742, 1, x_741);
return x_742;
}
}
}
}
default: 
{
lean_dec(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_743; lean_object* x_744; 
lean_dec(x_26);
x_743 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_744 = l_Lean_Meta_substCore(x_1, x_2, x_743, x_5, x_743, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_744, 1);
lean_inc(x_746);
lean_dec(x_744);
x_747 = lean_ctor_get(x_745, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_745, 1);
lean_inc(x_748);
lean_dec(x_745);
x_749 = x_4;
x_750 = lean_unsigned_to_nat(0u);
x_751 = l_Array_umapMAux___main___at___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___spec__25(x_747, x_750, x_749);
x_752 = x_751;
x_753 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_753, 0, x_748);
lean_ctor_set(x_753, 1, x_752);
lean_ctor_set(x_753, 2, x_747);
x_754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_6);
x_755 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_754, x_8, x_9, x_10, x_11, x_746);
return x_755;
}
else
{
uint8_t x_756; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_756 = !lean_is_exclusive(x_744);
if (x_756 == 0)
{
return x_744;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_744, 0);
x_758 = lean_ctor_get(x_744, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_744);
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
return x_759;
}
}
}
else
{
lean_object* x_760; 
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_760 = l_Lean_Meta_injectionCore(x_1, x_2, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; 
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
if (lean_obj_tag(x_761) == 0)
{
uint8_t x_762; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_762 = !lean_is_exclusive(x_760);
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; 
x_763 = lean_ctor_get(x_760, 0);
lean_dec(x_763);
x_764 = lean_box(0);
lean_ctor_set(x_760, 0, x_764);
return x_760;
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_765 = lean_ctor_get(x_760, 1);
lean_inc(x_765);
lean_dec(x_760);
x_766 = lean_box(0);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_765);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_768 = lean_ctor_get(x_760, 1);
lean_inc(x_768);
lean_dec(x_760);
x_769 = lean_ctor_get(x_761, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_761, 1);
lean_inc(x_770);
lean_dec(x_761);
x_771 = lean_nat_add(x_3, x_770);
lean_dec(x_770);
x_772 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_4);
lean_ctor_set(x_772, 2, x_5);
x_773 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_773, 0, x_772);
lean_ctor_set(x_773, 1, x_6);
x_774 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_771, x_773, x_8, x_9, x_10, x_11, x_768);
lean_dec(x_771);
return x_774;
}
}
else
{
uint8_t x_775; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_775 = !lean_is_exclusive(x_760);
if (x_775 == 0)
{
return x_760;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_776 = lean_ctor_get(x_760, 0);
x_777 = lean_ctor_get(x_760, 1);
lean_inc(x_777);
lean_inc(x_776);
lean_dec(x_760);
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_776);
lean_ctor_set(x_778, 1, x_777);
return x_778;
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
uint8_t x_779; 
lean_dec(x_32);
lean_dec(x_28);
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
x_779 = !lean_is_exclusive(x_34);
if (x_779 == 0)
{
return x_34;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_34, 0);
x_781 = lean_ctor_get(x_34, 1);
lean_inc(x_781);
lean_inc(x_780);
lean_dec(x_34);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
return x_782;
}
}
}
else
{
uint8_t x_783; 
lean_dec(x_28);
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
x_783 = !lean_is_exclusive(x_31);
if (x_783 == 0)
{
return x_31;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_31, 0);
x_785 = lean_ctor_get(x_31, 1);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_31);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
return x_786;
}
}
}
else
{
lean_object* x_787; lean_object* x_788; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
x_787 = lean_ctor_get(x_27, 1);
lean_inc(x_787);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_788 = l_Lean_Meta_clear(x_1, x_2, x_8, x_9, x_10, x_11, x_787);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec(x_788);
x_791 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_791, 0, x_789);
lean_ctor_set(x_791, 1, x_4);
lean_ctor_set(x_791, 2, x_5);
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_6);
x_793 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_3, x_792, x_8, x_9, x_10, x_11, x_790);
return x_793;
}
else
{
uint8_t x_794; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_794 = !lean_is_exclusive(x_788);
if (x_794 == 0)
{
return x_788;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_788, 0);
x_796 = lean_ctor_get(x_788, 1);
lean_inc(x_796);
lean_inc(x_795);
lean_dec(x_788);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
return x_797;
}
}
}
}
else
{
uint8_t x_798; 
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
x_798 = !lean_is_exclusive(x_27);
if (x_798 == 0)
{
return x_27;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_27, 0);
x_800 = lean_ctor_get(x_27, 1);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_27);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
return x_801;
}
}
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_802 = l_Lean_Expr_appFn_x21(x_13);
x_803 = l_Lean_Expr_appFn_x21(x_802);
lean_dec(x_802);
x_804 = l_Lean_Expr_appArg_x21(x_803);
lean_dec(x_803);
x_805 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
lean_inc(x_2);
x_806 = l_Lean_mkFVar(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_807 = l___private_Lean_Meta_AppBuilder_14__mkEqOfHEqImp(x_806, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_810 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_804, x_805, x_8, x_9, x_10, x_11, x_809);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_813 = l_Lean_LocalDecl_userName(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_814 = l_Lean_Meta_assert(x_1, x_813, x_811, x_808, x_8, x_9, x_10, x_11, x_812);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_814, 1);
lean_inc(x_816);
lean_dec(x_814);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_817 = l_Lean_Meta_clear(x_815, x_2, x_8, x_9, x_10, x_11, x_816);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
lean_dec(x_817);
x_820 = lean_unsigned_to_nat(1u);
x_821 = lean_nat_add(x_3, x_820);
x_822 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_822, 0, x_818);
lean_ctor_set(x_822, 1, x_4);
lean_ctor_set(x_822, 2, x_5);
x_823 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_6);
x_824 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_821, x_823, x_8, x_9, x_10, x_11, x_819);
lean_dec(x_821);
return x_824;
}
else
{
uint8_t x_825; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_825 = !lean_is_exclusive(x_817);
if (x_825 == 0)
{
return x_817;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_817, 0);
x_827 = lean_ctor_get(x_817, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_817);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_829 = !lean_is_exclusive(x_814);
if (x_829 == 0)
{
return x_814;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_830 = lean_ctor_get(x_814, 0);
x_831 = lean_ctor_get(x_814, 1);
lean_inc(x_831);
lean_inc(x_830);
lean_dec(x_814);
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
return x_832;
}
}
}
else
{
uint8_t x_833; 
lean_dec(x_808);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_833 = !lean_is_exclusive(x_810);
if (x_833 == 0)
{
return x_810;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_834 = lean_ctor_get(x_810, 0);
x_835 = lean_ctor_get(x_810, 1);
lean_inc(x_835);
lean_inc(x_834);
lean_dec(x_810);
x_836 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_836, 0, x_834);
lean_ctor_set(x_836, 1, x_835);
return x_836;
}
}
}
else
{
uint8_t x_837; 
lean_dec(x_805);
lean_dec(x_804);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_837 = !lean_is_exclusive(x_807);
if (x_837 == 0)
{
return x_807;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_838 = lean_ctor_get(x_807, 0);
x_839 = lean_ctor_get(x_807, 1);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_807);
x_840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_840, 0, x_838);
lean_ctor_set(x_840, 1, x_839);
return x_840;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unifyEqs ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__3;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_1, x_10);
lean_inc(x_2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
x_13 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
x_14 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_13, x_12, x_3, x_4, x_5, x_6, x_7);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
lean_dec(x_15);
x_21 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_intro1Core(x_18, x_21, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
lean_inc(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_27, 0, x_25);
lean_inc(x_26);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___boxed), 12, 6);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_11);
lean_closure_set(x_28, 3, x_19);
lean_closure_set(x_28, 4, x_20);
lean_closure_set(x_28, 5, x_17);
x_29 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_26, x_29, x_3, x_4, x_5, x_6, x_24);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_2);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___boxed), 2, 1);
lean_closure_set(x_35, 0, x_2);
x_36 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
x_37 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_36, x_35, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
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
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_empty___closed__1;
x_10 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(x_1, x_2, x_2, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Cases_10__unifyEqs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_10__unifyEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_23 = l_List_redLength___main___rarg(x_22);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean_dec(x_23);
x_25 = l_List_toArrayAux___main___rarg(x_22, x_24);
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
x_29 = l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(x_28, x_25, x_3, x_15, x_16);
lean_dec(x_16);
lean_dec(x_25);
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
x_32 = l___private_Lean_Meta_Tactic_Cases_8__toCasesSubgoals(x_30, x_25, x_3, x_15, x_16);
lean_dec(x_16);
lean_dec(x_25);
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
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_11 = l_Lean_mkFVar(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_box(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1___boxed), 11, 5);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___lambda__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after generalizeIndices");
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Cases_cases___lambda__1___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Meta_Cases_cases___lambda__1___closed__4;
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not applicable to the given hypothesis");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Cases_cases___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Cases_cases___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l___private_Lean_Meta_Tactic_Cases_5__mkCasesContext_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
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
x_15 = l_Lean_Meta_Cases_cases___lambda__2___closed__3;
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_25);
x_28 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1;
x_29 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_28, x_27, x_7, x_8, x_9, x_10, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 3);
lean_inc(x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(x_31, x_32, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l___private_Lean_Meta_Tactic_Cases_7__elimAuxIndices(x_25, x_35, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_Tactic_Cases_10__unifyEqs(x_33, x_38, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_38);
lean_dec(x_33);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
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
lean_dec(x_33);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
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
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
x_53 = l___private_Lean_Meta_Tactic_Cases_11__inductionCasesOn(x_3, x_1, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_18);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_Meta_Cases_cases(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_box(x_4);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Cases_cases___lambda__2___boxed), 11, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Cases_cases___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_Cases_cases___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_Cases_cases___lambda__2(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
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
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__5 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__5);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__6 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__1___closed__6);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1 = _init_l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cases_9__unifyEqsAux___main___closed__1);
l_Lean_Meta_Cases_cases___lambda__1___closed__1 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__1);
l_Lean_Meta_Cases_cases___lambda__1___closed__2 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__2);
l_Lean_Meta_Cases_cases___lambda__1___closed__3 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__3);
l_Lean_Meta_Cases_cases___lambda__1___closed__4 = _init_l_Lean_Meta_Cases_cases___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__1___closed__4);
l_Lean_Meta_Cases_cases___lambda__2___closed__1 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__1);
l_Lean_Meta_Cases_cases___lambda__2___closed__2 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__2);
l_Lean_Meta_Cases_cases___lambda__2___closed__3 = _init_l_Lean_Meta_Cases_cases___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Cases_cases___lambda__2___closed__3);
res = l___private_Lean_Meta_Tactic_Cases_12__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
