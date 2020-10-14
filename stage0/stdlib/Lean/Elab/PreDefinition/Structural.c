// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural
// Imports: Init Lean.Util.ForEachExpr Lean.Meta.ForEachExpr Lean.Meta.RecursorInfo Lean.Meta.Match.Match Lean.Elab.PreDefinition.Basic
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
extern lean_object* l_Lean_Meta_binductionOnSuffix;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__2(lean_object*);
uint8_t l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_addInstanceEntry___spec__11(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__3(lean_object*);
lean_object* l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__1(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2;
lean_object* l_Lean_Core_mkFreshUserName___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__16;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Match_Match_42__updateAlts___main___lambda__2___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__1(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafeRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__8;
extern lean_object* l_Lean_Elab_PreDefinition_inhabited;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__4;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__4;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__7;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__2;
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__3;
lean_object* l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__17;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8;
lean_object* l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1(lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__3;
lean_object* l_Lean_Elab_structuralRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__9;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__3;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__8;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix_match__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__5;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_brecOnSuffix;
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExprImp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__7;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__1;
lean_object* l___private_Lean_Meta_Basic_28__withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1;
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_ForEachExpr_visit___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__4(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2;
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__3(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14;
lean_object* l_Lean_Meta_forEachExpr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18;
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5;
lean_object* l_Lean_Elab_structuralRecursion___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__5;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__6;
lean_object* l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__14;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__15;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__6;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__4___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1;
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__7;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__2(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__3;
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_3362_(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__3___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__8;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__4(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_2__decLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__4;
size_t l_USize_mod(size_t, size_t);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1;
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__1;
lean_object* l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__13;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__2;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__1;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__1(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__15;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__7;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__3;
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16;
extern lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2;
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__9;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_mkAppM___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10;
lean_object* l_Lean_Meta_forEachExpr___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_decLevel___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(lean_object*, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__3(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix_match__1___rarg(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__2(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__2;
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__11;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__13;
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__11;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__3(lean_object*);
lean_object* l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_23__lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__3(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix_match__1___rarg), 2, 0);
return x_2;
}
}
uint8_t l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_1, x_4);
x_9 = lean_array_fget(x_2, x_4);
x_10 = lean_expr_eqv(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
}
}
}
uint8_t l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_le(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2(x_1, x_2, lean_box(0), x_7);
return x_8;
}
}
}
lean_object* l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_27; lean_object* x_28; uint8_t x_115; lean_object* x_116; lean_object* x_120; 
x_120 = lean_st_ref_get(x_4, x_6);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
x_124 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(x_122, x_3);
lean_dec(x_122);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
lean_free_object(x_120);
x_125 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = 1;
x_115 = x_126;
x_116 = x_123;
goto block_119;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_127);
x_129 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_128);
x_130 = lean_mk_array(x_128, x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_sub(x_128, x_131);
lean_dec(x_128);
lean_inc(x_3);
x_133 = l___private_Lean_Expr_3__getAppArgsAux___main(x_3, x_130, x_132);
x_134 = lean_st_ref_take(x_5, x_123);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_array_get_size(x_133);
x_138 = lean_nat_dec_lt(x_137, x_135);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_137);
x_139 = lean_st_ref_set(x_5, x_135, x_136);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_133, x_2);
lean_dec(x_133);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = 1;
x_115 = x_142;
x_116 = x_140;
goto block_119;
}
else
{
uint8_t x_143; 
x_143 = 0;
x_115 = x_143;
x_116 = x_140;
goto block_119;
}
}
else
{
uint8_t x_144; 
lean_dec(x_133);
lean_dec(x_3);
x_144 = !lean_is_exclusive(x_139);
if (x_144 == 0)
{
return x_139;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_139, 0);
x_146 = lean_ctor_get(x_139, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_139);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; 
lean_dec(x_135);
x_148 = lean_st_ref_set(x_5, x_137, x_136);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_133, x_2);
lean_dec(x_133);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = 1;
x_115 = x_151;
x_116 = x_149;
goto block_119;
}
else
{
uint8_t x_152; 
x_152 = 0;
x_115 = x_152;
x_116 = x_149;
goto block_119;
}
}
else
{
uint8_t x_153; 
lean_dec(x_133);
lean_dec(x_3);
x_153 = !lean_is_exclusive(x_148);
if (x_153 == 0)
{
return x_148;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_148, 0);
x_155 = lean_ctor_get(x_148, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_148);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_133);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_134);
if (x_157 == 0)
{
return x_134;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_134, 0);
x_159 = lean_ctor_get(x_134, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_134);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_161; 
lean_dec(x_3);
x_161 = lean_ctor_get(x_124, 0);
lean_inc(x_161);
lean_dec(x_124);
lean_ctor_set(x_120, 0, x_161);
return x_120;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_120, 0);
x_163 = lean_ctor_get(x_120, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_120);
x_164 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___main___spec__10(x_162, x_3);
lean_dec(x_162);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
x_165 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_165 == 0)
{
uint8_t x_166; 
x_166 = 1;
x_115 = x_166;
x_116 = x_163;
goto block_119;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Lean_Expr_getAppNumArgsAux___main(x_3, x_167);
x_169 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_168);
x_170 = lean_mk_array(x_168, x_169);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_sub(x_168, x_171);
lean_dec(x_168);
lean_inc(x_3);
x_173 = l___private_Lean_Expr_3__getAppArgsAux___main(x_3, x_170, x_172);
x_174 = lean_st_ref_take(x_5, x_163);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_array_get_size(x_173);
x_178 = lean_nat_dec_lt(x_177, x_175);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_177);
x_179 = lean_st_ref_set(x_5, x_175, x_176);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_173, x_2);
lean_dec(x_173);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = 1;
x_115 = x_182;
x_116 = x_180;
goto block_119;
}
else
{
uint8_t x_183; 
x_183 = 0;
x_115 = x_183;
x_116 = x_180;
goto block_119;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_173);
lean_dec(x_3);
x_184 = lean_ctor_get(x_179, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_186 = x_179;
} else {
 lean_dec_ref(x_179);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_175);
x_188 = lean_st_ref_set(x_5, x_177, x_176);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_173, x_2);
lean_dec(x_173);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = 1;
x_115 = x_191;
x_116 = x_189;
goto block_119;
}
else
{
uint8_t x_192; 
x_192 = 0;
x_115 = x_192;
x_116 = x_189;
goto block_119;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_173);
lean_dec(x_3);
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_195 = x_188;
} else {
 lean_dec_ref(x_188);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_173);
lean_dec(x_3);
x_197 = lean_ctor_get(x_174, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_174, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_199 = x_174;
} else {
 lean_dec_ref(x_174);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_3);
x_201 = lean_ctor_get(x_164, 0);
lean_inc(x_201);
lean_dec(x_164);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_163);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_3);
x_203 = !lean_is_exclusive(x_120);
if (x_203 == 0)
{
return x_120;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_120, 0);
x_205 = lean_ctor_get(x_120, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_120);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
block_26:
{
lean_object* x_9; 
x_9 = lean_st_ref_take(x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
x_12 = l_Std_HashMapImp_insert___at_Lean_Meta_ForEachExpr_visit___main___spec__1(x_10, x_3, x_7);
x_13 = lean_st_ref_set(x_4, x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_7);
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
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
block_114:
{
if (x_27 == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_29, x_4, x_5, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_30, x_4, x_5, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_7 = x_34;
x_8 = x_35;
goto block_26;
}
else
{
uint8_t x_36; 
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
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
lean_dec(x_30);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 6:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
x_46 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_44, x_4, x_5, x_28);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_45, x_4, x_5, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_7 = x_49;
x_8 = x_50;
goto block_26;
}
else
{
uint8_t x_51; 
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
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
lean_dec(x_45);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 0);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_46);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
x_61 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_59, x_4, x_5, x_28);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_60, x_4, x_5, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_7 = x_64;
x_8 = x_65;
goto block_26;
}
else
{
uint8_t x_66; 
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_60);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_61);
if (x_70 == 0)
{
return x_61;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_61, 0);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_61);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
case 8:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 3);
lean_inc(x_76);
x_77 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_74, x_4, x_5, x_28);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_75, x_4, x_5, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_76, x_4, x_5, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_7 = x_82;
x_8 = x_83;
goto block_26;
}
else
{
uint8_t x_84; 
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
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
lean_dec(x_76);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_79);
if (x_88 == 0)
{
return x_79;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_79, 0);
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_79);
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
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_77);
if (x_92 == 0)
{
return x_77;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_77, 0);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_77);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 10:
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_96, x_4, x_5, x_28);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_7 = x_98;
x_8 = x_99;
goto block_26;
}
else
{
uint8_t x_100; 
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_97);
if (x_100 == 0)
{
return x_97;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_97);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
case 11:
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_3, 2);
lean_inc(x_104);
x_105 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_104, x_4, x_5, x_28);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_7 = x_106;
x_8 = x_107;
goto block_26;
}
else
{
uint8_t x_108; 
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
default: 
{
lean_object* x_112; 
x_112 = lean_box(0);
x_7 = x_112;
x_8 = x_28;
goto block_26;
}
}
}
else
{
lean_object* x_113; 
x_113 = lean_box(0);
x_7 = x_113;
x_8 = x_28;
goto block_26;
}
}
block_119:
{
if (x_115 == 0)
{
uint8_t x_117; 
x_117 = 1;
x_27 = x_117;
x_28 = x_116;
goto block_114;
}
else
{
uint8_t x_118; 
x_118 = 0;
x_27 = x_118;
x_28 = x_116;
goto block_114;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_box(0);
x_6 = lean_st_mk_ref(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_HashMap_inhabited___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_3, x_11, x_7, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_11, x_14);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_7, x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
lean_object* l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ForEachExpr_visit___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(x_1, x_7, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_4 + x_10;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_nat_dec_lt(x_13, x_5);
if (x_14 == 0)
{
size_t x_15; size_t x_16; 
lean_dec(x_13);
x_15 = 1;
x_16 = x_4 + x_15;
x_4 = x_16;
goto _start;
}
else
{
size_t x_18; size_t x_19; 
lean_dec(x_5);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_13;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_array_get_size(x_2);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1(x_1, x_2, x_5, x_6, x_3);
return x_7;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_MetavarContext_exprDependsOn(x_11, x_1, x_2);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
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
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_MetavarContext_exprDependsOn(x_17, x_1, x_2);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_contains___at_Lean_Meta_addInstanceEntry___spec__11(x_1, x_2);
if (x_11 == 0)
{
if (x_5 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
x_17 = l_Lean_Expr_fvarId_x21(x_16);
lean_inc(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1___boxed), 7, 2);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1___boxed), 10, 4);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_18, x_19, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = 1;
x_31 = x_7 + x_30;
x_7 = x_31;
x_8 = x_29;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc_n(x_3, 2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2(x_2, x_3, x_4, x_5, x_1, x_12, x_13, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_36 = x_16;
} else {
 lean_dec_ref(x_16);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_3);
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
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1), 6, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1___boxed), 10, 4);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_16, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = 1;
x_29 = x_6 + x_28;
x_6 = x_29;
x_7 = x_27;
x_12 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___closed__1() {
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___closed__1;
lean_inc(x_2);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3(x_1, x_2, x_12, x_2, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_4 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1___boxed), 7, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_16);
lean_inc(x_2);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1___boxed), 9, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_17, x_18, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = 1;
x_30 = x_6 + x_29;
x_6 = x_30;
x_7 = x_28;
x_12 = x_27;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc_n(x_2, 2);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1(x_2, x_3, x_4, x_1, x_11, x_12, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_13, 0, x_32);
return x_13;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_35 = x_15;
} else {
 lean_dec_ref(x_15);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
}
else
{
uint8_t x_41; 
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1), 6, 1);
lean_closure_set(x_15, 0, x_14);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1___boxed), 9, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(x_15, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = 1;
x_28 = x_5 + x_27;
x_5 = x_28;
x_6 = x_26;
x_11 = x_25;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___closed__1;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2(x_1, x_12, x_2, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural recursion cannot be used");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3;
x_7 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_fvarId_x21(x_1);
x_8 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l_Lean_Meta_whnf___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 6);
x_26 = lean_ctor_get_uint8(x_8, 7);
lean_dec(x_8);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_28, 0, x_20);
lean_ctor_set_uint8(x_28, 1, x_21);
lean_ctor_set_uint8(x_28, 2, x_22);
lean_ctor_set_uint8(x_28, 3, x_23);
lean_ctor_set_uint8(x_28, 4, x_24);
lean_ctor_set_uint8(x_28, 5, x_27);
lean_ctor_set_uint8(x_28, 6, x_25);
lean_ctor_set_uint8(x_28, 7, x_26);
lean_ctor_set(x_2, 0, x_28);
x_29 = l_Lean_Meta_whnf___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_41 = lean_ctor_get_uint8(x_38, 0);
x_42 = lean_ctor_get_uint8(x_38, 1);
x_43 = lean_ctor_get_uint8(x_38, 2);
x_44 = lean_ctor_get_uint8(x_38, 3);
x_45 = lean_ctor_get_uint8(x_38, 4);
x_46 = lean_ctor_get_uint8(x_38, 6);
x_47 = lean_ctor_get_uint8(x_38, 7);
if (lean_is_exclusive(x_38)) {
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 0, 8);
} else {
 x_50 = x_48;
}
lean_ctor_set_uint8(x_50, 0, x_41);
lean_ctor_set_uint8(x_50, 1, x_42);
lean_ctor_set_uint8(x_50, 2, x_43);
lean_ctor_set_uint8(x_50, 3, x_44);
lean_ctor_set_uint8(x_50, 4, x_45);
lean_ctor_set_uint8(x_50, 5, x_49);
lean_ctor_set_uint8(x_50, 6, x_46);
lean_ctor_set_uint8(x_50, 7, x_47);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
lean_ctor_set(x_51, 2, x_40);
x_52 = l_Lean_Meta_whnf___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1(x_1, x_51, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
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
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
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
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Environment_contains(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Environment_contains(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PreDefinition.Structural");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.Structural.0.Lean.Elab.findRecArg.loop");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__1;
x_2 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__2;
x_3 = lean_unsigned_to_nat(101u);
x_4 = lean_unsigned_to_nat(117u);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__1(x_1, x_10, x_8);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Nat_Inhabited;
x_15 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__3;
x_16 = lean_panic_fn(x_14, x_15);
x_17 = x_16;
x_18 = lean_array_fset(x_9, x_2, x_17);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = x_20;
x_22 = lean_array_fset(x_9, x_2, x_21);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_22;
goto _start;
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_1, x_8);
x_10 = lean_expr_eqv(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 1;
return x_13;
}
}
}
uint8_t l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
lean_inc(x_2);
x_7 = l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__6(x_1, x_6, x_2, lean_box(0));
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_isFVar(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument #");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive datatype");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nand parameter");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ndepends on");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive family");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nand index");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ndepends on the non index");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive family and indices are not pairwise distinct");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive family and indices are not variables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_4);
lean_inc(x_5);
x_14 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_isLet(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_whnfD___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2(x_18, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_getAppFn___main(x_20);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_8, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_environment_find(x_28, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_10);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_4 = x_31;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 5)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_441; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Meta_brecOnSuffix;
lean_inc(x_36);
x_38 = lean_name_mk_string(x_36, x_37);
x_39 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(x_38, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_binductionOnSuffix;
lean_inc(x_36);
x_43 = lean_name_mk_string(x_36, x_42);
x_44 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(x_43, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_441 = lean_unbox(x_40);
lean_dec(x_40);
if (x_441 == 0)
{
uint8_t x_442; 
x_442 = 1;
x_47 = x_442;
goto block_440;
}
else
{
uint8_t x_443; 
x_443 = 0;
x_47 = x_443;
goto block_440;
}
block_440:
{
if (x_47 == 0)
{
uint8_t x_48; uint8_t x_49; 
x_48 = lean_ctor_get_uint8(x_34, sizeof(void*)*5 + 2);
if (x_48 == 0)
{
uint8_t x_434; 
lean_dec(x_45);
x_434 = 0;
x_49 = x_434;
goto block_433;
}
else
{
uint8_t x_435; 
x_435 = lean_unbox(x_45);
lean_dec(x_45);
if (x_435 == 0)
{
x_49 = x_48;
goto block_433;
}
else
{
uint8_t x_436; 
x_436 = 0;
x_49 = x_436;
goto block_433;
}
}
block_433:
{
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_293; uint8_t x_359; lean_object* x_426; uint8_t x_427; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Expr_getAppNumArgsAux___main(x_20, x_50);
x_52 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_51);
x_53 = lean_mk_array(x_51, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_51, x_54);
lean_dec(x_51);
lean_inc(x_20);
x_56 = l___private_Lean_Expr_3__getAppArgsAux___main(x_20, x_53, x_55);
x_57 = lean_ctor_get(x_34, 1);
lean_inc(x_57);
lean_inc(x_57);
lean_inc(x_56);
x_58 = l_Array_extract___rarg(x_56, x_50, x_57);
x_59 = lean_array_get_size(x_56);
x_60 = l_Array_extract___rarg(x_56, x_57, x_59);
x_426 = lean_array_get_size(x_60);
x_427 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__7(x_20, x_34, x_60, x_426, x_50);
lean_dec(x_426);
lean_dec(x_34);
if (x_427 == 0)
{
uint8_t x_428; 
x_428 = 0;
x_359 = x_428;
goto block_425;
}
else
{
uint8_t x_429; 
x_429 = 1;
x_359 = x_429;
goto block_425;
}
block_292:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_inc(x_61);
lean_inc(x_2);
x_62 = l_Array_extract___rarg(x_2, x_50, x_61);
lean_inc(x_2);
x_63 = l_Array_extract___rarg(x_2, x_61, x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
lean_inc(x_63);
x_64 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f(x_63, x_60, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_63);
x_67 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f(x_63, x_58, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_20);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_60);
x_70 = x_60;
x_71 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(x_63, x_50, x_70);
x_72 = x_71;
x_73 = lean_array_get_size(x_62);
x_74 = lean_nat_sub(x_4, x_73);
lean_dec(x_73);
x_75 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_75, 0, x_62);
lean_ctor_set(x_75, 1, x_63);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_72);
lean_ctor_set(x_75, 4, x_36);
lean_ctor_set(x_75, 5, x_24);
lean_ctor_set(x_75, 6, x_58);
lean_ctor_set(x_75, 7, x_60);
lean_ctor_set_uint8(x_75, sizeof(void*)*8, x_48);
x_76 = lean_nat_add(x_4, x_54);
lean_dec(x_4);
x_77 = lean_st_ref_get(x_8, x_69);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_get(x_6, x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = lean_apply_6(x_3, x_75, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_80, x_5, x_6, x_7, x_8, x_91);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_84, x_5, x_6, x_7, x_8, x_93);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_dec(x_90);
x_98 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_76, x_5, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
lean_dec(x_97);
lean_dec(x_96);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_98);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_98, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_103, 1);
x_108 = lean_ctor_get(x_103, 0);
lean_dec(x_108);
x_109 = l_Lean_MessageData_ofList___closed__3;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_97);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
lean_ctor_set(x_103, 1, x_112);
lean_ctor_set(x_103, 0, x_96);
return x_98;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
lean_dec(x_103);
x_114 = l_Lean_MessageData_ofList___closed__3;
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_97);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_113);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_96);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_98, 0, x_118);
return x_98;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
lean_dec(x_98);
x_120 = lean_ctor_get(x_103, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_121 = x_103;
} else {
 lean_dec_ref(x_103);
 x_121 = lean_box(0);
}
x_122 = l_Lean_MessageData_ofList___closed__3;
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_97);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_120);
if (lean_is_scalar(x_121)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_121;
}
lean_ctor_set(x_126, 0, x_96);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_119);
return x_127;
}
}
else
{
uint8_t x_128; 
lean_dec(x_97);
lean_dec(x_96);
x_128 = !lean_is_exclusive(x_98);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_98, 0);
lean_dec(x_129);
return x_98;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_98, 1);
lean_inc(x_130);
lean_dec(x_98);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_103);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_94);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_94, 0);
lean_dec(x_133);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 0, x_90);
return x_94;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_94, 1);
lean_inc(x_134);
lean_dec(x_94);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_90);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_36);
lean_dec(x_24);
x_136 = lean_ctor_get(x_68, 0);
lean_inc(x_136);
lean_dec(x_68);
x_137 = lean_ctor_get(x_67, 1);
lean_inc(x_137);
lean_dec(x_67);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_nat_add(x_4, x_54);
lean_dec(x_4);
lean_inc(x_140);
x_141 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_140);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4;
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_indentExpr(x_20);
x_148 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6;
x_150 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_indentExpr(x_138);
x_152 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8;
x_154 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_indentExpr(x_139);
x_156 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_158 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_st_ref_get(x_8, x_137);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_st_ref_get(x_6, x_161);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_158, x_5, x_6, x_7, x_8, x_165);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_162, x_5, x_6, x_7, x_8, x_169);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_166, x_5, x_6, x_7, x_8, x_171);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_ctor_get(x_168, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
lean_dec(x_168);
x_176 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_140, x_5, x_6, x_7, x_8, x_173);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
lean_dec(x_175);
lean_dec(x_174);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
return x_176;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_176);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
else
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_176);
if (x_182 == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_176, 0);
lean_dec(x_183);
x_184 = !lean_is_exclusive(x_181);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_181, 1);
x_186 = lean_ctor_get(x_181, 0);
lean_dec(x_186);
x_187 = l_Lean_MessageData_ofList___closed__3;
x_188 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_188, 0, x_175);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_185);
lean_ctor_set(x_181, 1, x_190);
lean_ctor_set(x_181, 0, x_174);
return x_176;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_191 = lean_ctor_get(x_181, 1);
lean_inc(x_191);
lean_dec(x_181);
x_192 = l_Lean_MessageData_ofList___closed__3;
x_193 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_193, 0, x_175);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_191);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_174);
lean_ctor_set(x_196, 1, x_195);
lean_ctor_set(x_176, 0, x_196);
return x_176;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_197 = lean_ctor_get(x_176, 1);
lean_inc(x_197);
lean_dec(x_176);
x_198 = lean_ctor_get(x_181, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_199 = x_181;
} else {
 lean_dec_ref(x_181);
 x_199 = lean_box(0);
}
x_200 = l_Lean_MessageData_ofList___closed__3;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_175);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_198);
if (lean_is_scalar(x_199)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_199;
}
lean_ctor_set(x_204, 0, x_174);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_197);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_dec(x_175);
lean_dec(x_174);
x_206 = !lean_is_exclusive(x_176);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_176, 0);
lean_dec(x_207);
return x_176;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_176, 1);
lean_inc(x_208);
lean_dec(x_176);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_181);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_67);
if (x_210 == 0)
{
return x_67;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_67, 0);
x_212 = lean_ctor_get(x_67, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_67);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_36);
lean_dec(x_24);
x_214 = lean_ctor_get(x_65, 0);
lean_inc(x_214);
lean_dec(x_65);
x_215 = lean_ctor_get(x_64, 1);
lean_inc(x_215);
lean_dec(x_64);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_nat_add(x_4, x_54);
lean_dec(x_4);
lean_inc(x_218);
x_219 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_218);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_222 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
x_223 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10;
x_224 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_indentExpr(x_20);
x_226 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12;
x_228 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lean_indentExpr(x_216);
x_230 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14;
x_232 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_indentExpr(x_217);
x_234 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_236 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_st_ref_get(x_8, x_215);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_st_ref_get(x_6, x_239);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
lean_dec(x_242);
x_245 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_236, x_5, x_6, x_7, x_8, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_240, x_5, x_6, x_7, x_8, x_247);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_244, x_5, x_6, x_7, x_8, x_249);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_ctor_get(x_246, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_246, 1);
lean_inc(x_253);
lean_dec(x_246);
x_254 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_218, x_5, x_6, x_7, x_8, x_251);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
lean_dec(x_253);
lean_dec(x_252);
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
return x_254;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_254);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
else
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_254, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_254);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_254, 0);
lean_dec(x_261);
x_262 = !lean_is_exclusive(x_259);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_259, 1);
x_264 = lean_ctor_get(x_259, 0);
lean_dec(x_264);
x_265 = l_Lean_MessageData_ofList___closed__3;
x_266 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_266, 0, x_253);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_263);
lean_ctor_set(x_259, 1, x_268);
lean_ctor_set(x_259, 0, x_252);
return x_254;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_259, 1);
lean_inc(x_269);
lean_dec(x_259);
x_270 = l_Lean_MessageData_ofList___closed__3;
x_271 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_271, 0, x_253);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
x_273 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_269);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_252);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_254, 0, x_274);
return x_254;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_275 = lean_ctor_get(x_254, 1);
lean_inc(x_275);
lean_dec(x_254);
x_276 = lean_ctor_get(x_259, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_277 = x_259;
} else {
 lean_dec_ref(x_259);
 x_277 = lean_box(0);
}
x_278 = l_Lean_MessageData_ofList___closed__3;
x_279 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_279, 0, x_253);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
x_281 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_276);
if (lean_is_scalar(x_277)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_277;
}
lean_ctor_set(x_282, 0, x_252);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_275);
return x_283;
}
}
else
{
uint8_t x_284; 
lean_dec(x_253);
lean_dec(x_252);
x_284 = !lean_is_exclusive(x_254);
if (x_284 == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_254, 0);
lean_dec(x_285);
return x_254;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_254, 1);
lean_inc(x_286);
lean_dec(x_254);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_259);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_288 = !lean_is_exclusive(x_64);
if (x_288 == 0)
{
return x_64;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_64, 0);
x_290 = lean_ctor_get(x_64, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_64);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
block_358:
{
if (x_293 == 0)
{
lean_object* x_294; uint8_t x_295; 
x_294 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos(x_2, x_60);
x_295 = lean_nat_dec_lt(x_294, x_1);
if (x_295 == 0)
{
lean_dec(x_294);
lean_inc(x_1);
x_61 = x_1;
goto block_292;
}
else
{
x_61 = x_294;
goto block_292;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_10);
x_296 = lean_nat_add(x_4, x_54);
lean_dec(x_4);
lean_inc(x_296);
x_297 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_296);
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_300 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
x_301 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16;
x_302 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_indentExpr(x_20);
x_304 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_st_ref_get(x_8, x_46);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_st_ref_get(x_6, x_309);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
lean_dec(x_312);
x_315 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_306, x_5, x_6, x_7, x_8, x_313);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_310, x_5, x_6, x_7, x_8, x_317);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_314, x_5, x_6, x_7, x_8, x_319);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_ctor_get(x_316, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_316, 1);
lean_inc(x_323);
lean_dec(x_316);
x_324 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_296, x_5, x_6, x_7, x_8, x_321);
if (lean_obj_tag(x_324) == 0)
{
uint8_t x_325; 
lean_dec(x_323);
lean_dec(x_322);
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
return x_324;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_324, 0);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_324);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
else
{
lean_object* x_329; 
x_329 = lean_ctor_get(x_324, 0);
lean_inc(x_329);
if (lean_obj_tag(x_329) == 0)
{
uint8_t x_330; 
x_330 = !lean_is_exclusive(x_324);
if (x_330 == 0)
{
lean_object* x_331; uint8_t x_332; 
x_331 = lean_ctor_get(x_324, 0);
lean_dec(x_331);
x_332 = !lean_is_exclusive(x_329);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_333 = lean_ctor_get(x_329, 1);
x_334 = lean_ctor_get(x_329, 0);
lean_dec(x_334);
x_335 = l_Lean_MessageData_ofList___closed__3;
x_336 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_336, 0, x_323);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_333);
lean_ctor_set(x_329, 1, x_338);
lean_ctor_set(x_329, 0, x_322);
return x_324;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_339 = lean_ctor_get(x_329, 1);
lean_inc(x_339);
lean_dec(x_329);
x_340 = l_Lean_MessageData_ofList___closed__3;
x_341 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_341, 0, x_323);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
x_343 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_339);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_322);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_324, 0, x_344);
return x_324;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_345 = lean_ctor_get(x_324, 1);
lean_inc(x_345);
lean_dec(x_324);
x_346 = lean_ctor_get(x_329, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_347 = x_329;
} else {
 lean_dec_ref(x_329);
 x_347 = lean_box(0);
}
x_348 = l_Lean_MessageData_ofList___closed__3;
x_349 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_349, 0, x_323);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_348);
x_351 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_346);
if (lean_is_scalar(x_347)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_347;
}
lean_ctor_set(x_352, 0, x_322);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_345);
return x_353;
}
}
else
{
uint8_t x_354; 
lean_dec(x_323);
lean_dec(x_322);
x_354 = !lean_is_exclusive(x_324);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_324, 0);
lean_dec(x_355);
return x_324;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_324, 1);
lean_inc(x_356);
lean_dec(x_324);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_329);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
}
}
block_425:
{
if (x_359 == 0)
{
uint8_t x_360; 
x_360 = l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(x_60, x_50);
if (x_360 == 0)
{
uint8_t x_361; 
x_361 = 1;
x_293 = x_361;
goto block_358;
}
else
{
uint8_t x_362; 
x_362 = 0;
x_293 = x_362;
goto block_358;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_10);
x_363 = lean_nat_add(x_4, x_54);
lean_dec(x_4);
lean_inc(x_363);
x_364 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_363);
x_365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_365, 0, x_364);
x_366 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_367 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_368 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18;
x_369 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_indentExpr(x_20);
x_371 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_373 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_374 = lean_st_ref_get(x_8, x_46);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_377 = lean_ctor_get(x_375, 0);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_st_ref_get(x_6, x_376);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
lean_dec(x_379);
x_382 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_373, x_5, x_6, x_7, x_8, x_380);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_377, x_5, x_6, x_7, x_8, x_384);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec(x_385);
x_387 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_381, x_5, x_6, x_7, x_8, x_386);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_ctor_get(x_383, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_383, 1);
lean_inc(x_390);
lean_dec(x_383);
x_391 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_363, x_5, x_6, x_7, x_8, x_388);
if (lean_obj_tag(x_391) == 0)
{
uint8_t x_392; 
lean_dec(x_390);
lean_dec(x_389);
x_392 = !lean_is_exclusive(x_391);
if (x_392 == 0)
{
return x_391;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_391, 0);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_391);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
else
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_391, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
uint8_t x_397; 
x_397 = !lean_is_exclusive(x_391);
if (x_397 == 0)
{
lean_object* x_398; uint8_t x_399; 
x_398 = lean_ctor_get(x_391, 0);
lean_dec(x_398);
x_399 = !lean_is_exclusive(x_396);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_400 = lean_ctor_get(x_396, 1);
x_401 = lean_ctor_get(x_396, 0);
lean_dec(x_401);
x_402 = l_Lean_MessageData_ofList___closed__3;
x_403 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_403, 0, x_390);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_402);
x_405 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_400);
lean_ctor_set(x_396, 1, x_405);
lean_ctor_set(x_396, 0, x_389);
return x_391;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_406 = lean_ctor_get(x_396, 1);
lean_inc(x_406);
lean_dec(x_396);
x_407 = l_Lean_MessageData_ofList___closed__3;
x_408 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_408, 0, x_390);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
x_410 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_406);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_389);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_391, 0, x_411);
return x_391;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_412 = lean_ctor_get(x_391, 1);
lean_inc(x_412);
lean_dec(x_391);
x_413 = lean_ctor_get(x_396, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_414 = x_396;
} else {
 lean_dec_ref(x_396);
 x_414 = lean_box(0);
}
x_415 = l_Lean_MessageData_ofList___closed__3;
x_416 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_416, 0, x_390);
lean_ctor_set(x_416, 1, x_415);
x_417 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
x_418 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_413);
if (lean_is_scalar(x_414)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_414;
}
lean_ctor_set(x_419, 0, x_389);
lean_ctor_set(x_419, 1, x_418);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_412);
return x_420;
}
}
else
{
uint8_t x_421; 
lean_dec(x_390);
lean_dec(x_389);
x_421 = !lean_is_exclusive(x_391);
if (x_421 == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_391, 0);
lean_dec(x_422);
return x_391;
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_391, 1);
lean_inc(x_423);
lean_dec(x_391);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_396);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_10);
x_430 = lean_unsigned_to_nat(1u);
x_431 = lean_nat_add(x_4, x_430);
lean_dec(x_4);
x_4 = x_431;
x_9 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_45);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_10);
x_437 = lean_unsigned_to_nat(1u);
x_438 = lean_nat_add(x_4, x_437);
lean_dec(x_4);
x_4 = x_438;
x_9 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; 
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_10);
x_444 = lean_unsigned_to_nat(1u);
x_445 = lean_nat_add(x_4, x_444);
lean_dec(x_4);
x_4 = x_445;
x_9 = x_27;
goto _start;
}
}
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
x_447 = lean_unsigned_to_nat(1u);
x_448 = lean_nat_add(x_4, x_447);
lean_dec(x_4);
x_4 = x_448;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_450; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_450 = !lean_is_exclusive(x_19);
if (x_450 == 0)
{
return x_19;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_19, 0);
x_452 = lean_ctor_get(x_19, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_19);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
lean_object* x_454; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_454 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg(x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_454;
}
}
else
{
uint8_t x_455; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_455 = !lean_is_exclusive(x_14);
if (x_455 == 0)
{
return x_14;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_14, 0);
x_457 = lean_ctor_get(x_14, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_14);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; size_t x_97; size_t x_98; lean_object* x_99; size_t x_100; uint8_t x_101; 
x_97 = lean_ptr_addr(x_3);
x_98 = x_2 == 0 ? 0 : x_97 % x_2;
x_99 = lean_array_uget(x_4, x_98);
x_100 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_101 = x_100 == x_97;
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
lean_inc(x_3);
x_102 = lean_array_uset(x_4, x_98, x_3);
x_103 = 0;
x_5 = x_103;
x_6 = x_102;
goto block_96;
}
else
{
uint8_t x_104; 
x_104 = 1;
x_5 = x_104;
x_6 = x_4;
goto block_96;
}
block_96:
{
if (x_5 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isConstOf(x_3, x_1);
if (x_7 == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(x_1, x_2, x_8, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_3 = x_9;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_21 = x_11;
} else {
 lean_dec_ref(x_11);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
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
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(x_1, x_2, x_24, x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_3 = x_25;
x_4 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_25);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_37 = x_27;
} else {
 lean_dec_ref(x_27);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
case 7:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
lean_dec(x_3);
x_42 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(x_1, x_2, x_40, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_3 = x_41;
x_4 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_41);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
x_59 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(x_1, x_2, x_56, x_6);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(x_1, x_2, x_57, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_3 = x_58;
x_4 = x_64;
goto _start;
}
else
{
uint8_t x_66; 
lean_dec(x_58);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_62;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_62, 0, x_70);
return x_62;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_58);
lean_dec(x_57);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_59, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_59;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_60, 0);
lean_inc(x_79);
lean_dec(x_60);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_59, 0, x_80);
return x_59;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
lean_dec(x_59);
x_82 = lean_ctor_get(x_60, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_83 = x_60;
} else {
 lean_dec_ref(x_60);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
case 10:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
lean_dec(x_3);
x_3 = x_86;
x_4 = x_6;
goto _start;
}
case 11:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_3, 2);
lean_inc(x_88);
lean_dec(x_3);
x_3 = x_88;
x_4 = x_6;
goto _start;
}
default: 
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_6);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_3);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_6);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_3);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_FindImpl_initCache;
x_5 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_forEachExprImp_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_forEachExpr___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___rarg___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_forEachExprImp_x27(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of recursive application");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isAppOf(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_indentExpr(x_2);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_2);
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_2);
x_11 = l_Lean_Meta_forEachExpr___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___spec__1(x_2, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toBelow failed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__3;
x_7 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PProd");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_usize(x_7, 2);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1;
x_18 = lean_string_dec_eq(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2;
x_20 = lean_string_dec_eq(x_15, x_19);
lean_dec(x_15);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
x_21 = lean_apply_1(x_4, x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_1);
x_22 = lean_box_uint64(x_14);
x_23 = lean_box_uint64(x_12);
x_24 = lean_box_uint64(x_10);
x_25 = lean_box_usize(x_16);
x_26 = lean_apply_7(x_3, x_13, x_22, x_11, x_23, x_9, x_24, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box_uint64(x_14);
x_28 = lean_box_uint64(x_12);
x_29 = lean_box_uint64(x_10);
x_30 = lean_box_usize(x_16);
x_31 = lean_apply_7(x_2, x_13, x_27, x_11, x_28, x_9, x_29, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_apply_1(x_4, x_1);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_apply_1(x_4, x_1);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_apply_1(x_4, x_1);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_apply_1(x_4, x_1);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_apply_1(x_4, x_1);
return x_36;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 3);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_10);
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Std_PersistentArray_push___rarg(x_19, x_21);
lean_ctor_set(x_14, 0, x_22);
x_23 = lean_st_ref_set(x_6, x_13, x_15);
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
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_10);
lean_inc(x_8);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_31, x_33);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_30);
lean_ctor_set(x_13, 3, x_35);
x_36 = lean_st_ref_set(x_6, x_13, x_15);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
x_43 = lean_ctor_get(x_13, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_44 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_46 = x_14;
} else {
 lean_dec_ref(x_14);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_10);
lean_inc(x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_PersistentArray_push___rarg(x_45, x_48);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(0, 1, 1);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_44);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_st_ref_set(x_6, x_51, x_15);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_checkTraceOption(x_7, x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
lean_inc(x_1);
x_17 = l___private_Lean_Expr_3__getAppArgsAux___main(x_1, x_14, x_16);
x_18 = lean_array_get_size(x_4);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_le(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_nat_sub(x_19, x_18);
lean_dec(x_18);
x_27 = l_Array_extract___rarg(x_17, x_26, x_19);
x_28 = l_Lean_Expr_replaceFVars(x_5, x_4, x_27);
if (lean_obj_tag(x_28) == 5)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Expr_getAppFn___main(x_29);
lean_dec(x_29);
x_32 = lean_expr_eqv(x_31, x_2);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_1);
x_33 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_38 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__2(x_30, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_27);
lean_dec(x_3);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_11, x_3);
lean_dec(x_27);
lean_ctor_set(x_38, 0, x_49);
return x_38;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_11, x_3);
lean_dec(x_27);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_38);
if (x_53 == 0)
{
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
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
lean_object* x_57; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_1);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_57;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("left");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("right");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fst");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("snd");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("belowDict: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", arg: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_whnf___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_124; lean_object* x_125; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_139 = lean_st_ref_get(x_8, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 3);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = 0;
x_124 = x_144;
x_125 = x_143;
goto block_138;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
x_146 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_147 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_146, x_5, x_6, x_7, x_8, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_unbox(x_148);
lean_dec(x_148);
x_124 = x_150;
x_125 = x_149;
goto block_138;
}
block_123:
{
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 5)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1;
x_22 = lean_string_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2;
x_24 = lean_string_dec_eq(x_20, x_23);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_18);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed), 10, 3);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_4);
x_26 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(x_11, x_25, x_5, x_6, x_7, x_8, x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_4);
x_29 = lean_st_ref_get(x_8, x_13);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_6, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__3;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_38 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___spec__1(x_37, x_28, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_41 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux(x_1, x_19, x_3, x_39, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_32, x_5, x_6, x_7, x_8, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_36, x_5, x_6, x_7, x_8, x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_48 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___spec__1(x_47, x_28, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_2 = x_18;
x_4 = x_49;
x_9 = x_50;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_19);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_dec(x_38);
x_57 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_32, x_5, x_6, x_7, x_8, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_36, x_5, x_6, x_7, x_8, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___spec__1(x_61, x_28, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_2 = x_18;
x_4 = x_63;
x_9 = x_64;
goto _start;
}
else
{
uint8_t x_66; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_20);
lean_dec(x_11);
x_70 = l_Lean_mkOptionalNode___closed__2;
x_71 = lean_array_push(x_70, x_4);
x_72 = lean_st_ref_get(x_8, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_get(x_6, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_71);
x_81 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___spec__1(x_80, x_71, x_5, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_84 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux(x_1, x_19, x_3, x_82, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_75, x_5, x_6, x_7, x_8, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_79, x_5, x_6, x_7, x_8, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_91 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___spec__1(x_90, x_71, x_5, x_6, x_7, x_8, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_2 = x_18;
x_4 = x_92;
x_9 = x_93;
goto _start;
}
else
{
uint8_t x_95; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_91, 0);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_91);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_19);
x_99 = lean_ctor_get(x_81, 1);
lean_inc(x_99);
lean_dec(x_81);
x_100 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_75, x_5, x_6, x_7, x_8, x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_79, x_5, x_6, x_7, x_8, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_105 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___spec__1(x_104, x_71, x_5, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_2 = x_18;
x_4 = x_106;
x_9 = x_107;
goto _start;
}
else
{
uint8_t x_109; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_105);
if (x_109 == 0)
{
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_105, 0);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_105);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
x_113 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed), 10, 3);
lean_closure_set(x_113, 0, x_3);
lean_closure_set(x_113, 1, x_1);
lean_closure_set(x_113, 2, x_4);
x_114 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(x_11, x_113, x_5, x_6, x_7, x_8, x_13);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_16);
lean_dec(x_14);
x_115 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed), 10, 3);
lean_closure_set(x_115, 0, x_3);
lean_closure_set(x_115, 1, x_1);
lean_closure_set(x_115, 2, x_4);
x_116 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(x_11, x_115, x_5, x_6, x_7, x_8, x_13);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_15);
lean_dec(x_14);
x_117 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed), 10, 3);
lean_closure_set(x_117, 0, x_3);
lean_closure_set(x_117, 1, x_1);
lean_closure_set(x_117, 2, x_4);
x_118 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(x_11, x_117, x_5, x_6, x_7, x_8, x_13);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_14);
x_119 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed), 10, 3);
lean_closure_set(x_119, 0, x_3);
lean_closure_set(x_119, 1, x_1);
lean_closure_set(x_119, 2, x_4);
x_120 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(x_11, x_119, x_5, x_6, x_7, x_8, x_13);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed), 10, 3);
lean_closure_set(x_121, 0, x_3);
lean_closure_set(x_121, 1, x_1);
lean_closure_set(x_121, 2, x_4);
x_122 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__1___rarg(x_11, x_121, x_5, x_6, x_7, x_8, x_13);
return x_122;
}
}
block_138:
{
if (x_124 == 0)
{
x_13 = x_125;
goto block_123;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_inc(x_11);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_11);
x_127 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__14;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__16;
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_3);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_3);
x_132 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_134 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_136 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_135, x_134, x_5, x_6, x_7, x_8, x_125);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_13 = x_137;
goto block_123;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_10);
if (x_151 == 0)
{
return x_10;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_10, 0);
x_153 = lean_ctor_get(x_10, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_10);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Core_mkFreshUserName___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_CoreM_1__mkFreshNameImp(x_1, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_21__forallBoundedTelescopeImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_6);
x_12 = l_Lean_mkApp(x_1, x_6);
x_13 = l_Array_extract___rarg(x_2, x_3, x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_13, x_13, x_14, x_12);
lean_dec(x_13);
x_16 = lean_apply_7(x_5, x_6, x_15, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("C");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Expr_Inhabited;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_6, x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__2;
x_20 = l___private_Lean_CoreM_1__mkFreshNameImp(x_19, x_10, x_11, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__1), 11, 5);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
x_24 = 0;
x_25 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__4___rarg(x_21, x_24, x_17, x_23, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected 'below' type");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_array_set(x_5, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
lean_dec(x_6);
x_4 = x_12;
x_5 = x_14;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_1, x_18);
x_20 = lean_array_get_size(x_5);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_indentExpr(x_3);
x_23 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_26, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_33 = l_Array_extract___rarg(x_5, x_32, x_1);
x_34 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_33, x_33, x_32, x_4);
lean_dec(x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_34);
x_35 = l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_34, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___boxed), 12, 5);
lean_closure_set(x_38, 0, x_34);
lean_closure_set(x_38, 1, x_5);
lean_closure_set(x_38, 2, x_19);
lean_closure_set(x_38, 3, x_20);
lean_closure_set(x_38, 4, x_2);
x_39 = l___private_Lean_Meta_Match_Match_42__updateAlts___main___lambda__2___closed__1;
x_40 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(x_36, x_39, x_38, x_7, x_8, x_9, x_10, x_37);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg), 11, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("belowType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_21; lean_object* x_22; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_32 = lean_st_ref_get(x_7, x_11);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = 0;
x_21 = x_37;
x_22 = x_36;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_40 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_39, x_4, x_5, x_6, x_7, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_21 = x_43;
x_22 = x_42;
goto block_31;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_13);
x_15 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_10);
x_19 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg(x_2, x_3, x_10, x_10, x_16, x_18, x_4, x_5, x_6, x_7, x_12);
return x_19;
}
block_31:
{
if (x_21 == 0)
{
x_12 = x_22;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_10);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_10);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_29 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_28, x_27, x_4, x_5, x_6, x_7, x_22);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_12 = x_30;
goto block_20;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_9);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Core_mkFreshUserName___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_mkFreshUserName___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux(x_3, x_4, x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_5(x_8, x_1, x_2, x_10, x_11, x_13);
return x_14;
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_6(x_3, x_1, x_2, x_15, x_16, x_17, x_19);
return x_20;
}
case 7:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_25 = lean_box_uint64(x_24);
x_26 = lean_apply_6(x_4, x_1, x_2, x_21, x_22, x_23, x_25);
return x_26;
}
case 8:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
x_31 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_dec(x_2);
x_32 = lean_box_uint64(x_31);
x_33 = lean_apply_6(x_5, x_1, x_27, x_28, x_29, x_30, x_32);
return x_33;
}
case 10:
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_4(x_6, x_1, x_34, x_35, x_37);
return x_38;
}
case 11:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_43 = lean_box_uint64(x_42);
x_44 = lean_apply_5(x_7, x_1, x_39, x_40, x_41, x_43);
return x_44;
}
default: 
{
lean_object* x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = lean_apply_2(x_9, x_1, x_2);
return x_45;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__3___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_5;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_5, x_4, x_16);
x_18 = x_15;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_17, x_4, x_24);
lean_dec(x_4);
x_4 = x_23;
x_5 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_5, x_6);
x_11 = lean_nat_dec_eq(x_3, x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
if (x_11 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 3);
x_15 = l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_14, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_push(x_7, x_10);
x_6 = x_13;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_10);
x_6 = x_13;
goto _start;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
x_6 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to eliminate recursive application");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("insufficient number of parameters at recursive application ");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = x_6;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_17);
x_20 = x_19;
x_21 = lean_apply_5(x_20, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_23, x_23, x_18, x_15);
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
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_25, x_25, x_18, x_15);
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
lean_dec(x_15);
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
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_array_get_size(x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_50 = lean_nat_add(x_38, x_39);
x_51 = lean_array_get_size(x_6);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_Expr_Inhabited;
x_54 = lean_array_get(x_53, x_6, x_50);
lean_dec(x_50);
x_55 = lean_ctor_get(x_2, 6);
lean_inc(x_55);
x_56 = lean_array_get_size(x_55);
lean_dec(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_56, x_54, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_40 = x_58;
x_41 = x_59;
goto block_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_2);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_indentExpr(x_4);
x_62 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_65, x_8, x_9, x_10, x_11, x_60);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_71 = l_Lean_indentExpr(x_4);
x_72 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_75, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
block_49:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_array_get_size(x_6);
lean_inc(x_6);
x_43 = l_Array_extract___rarg(x_6, x_38, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_empty___closed__1;
x_46 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_39, x_43, x_43, x_44, x_45);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_2);
x_47 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_46, x_46, x_44, x_40);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
}
}
case 1:
{
uint8_t x_81; 
lean_dec(x_7);
x_81 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = x_6;
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_87, 0, x_1);
lean_closure_set(x_87, 1, x_2);
lean_closure_set(x_87, 2, x_3);
lean_closure_set(x_87, 3, x_86);
lean_closure_set(x_87, 4, x_85);
x_88 = x_87;
x_89 = lean_apply_5(x_88, x_8, x_9, x_10, x_11, x_84);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_91, x_91, x_86, x_83);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_93, x_93, x_86, x_83);
lean_dec(x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_83);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
return x_82;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_82, 0);
x_103 = lean_ctor_get(x_82, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_82);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_5);
lean_dec(x_1);
x_105 = lean_ctor_get(x_2, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
x_118 = lean_nat_add(x_106, x_107);
x_119 = lean_array_get_size(x_6);
x_120 = lean_nat_dec_le(x_119, x_118);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Lean_Expr_Inhabited;
x_122 = lean_array_get(x_121, x_6, x_118);
lean_dec(x_118);
x_123 = lean_ctor_get(x_2, 6);
lean_inc(x_123);
x_124 = lean_array_get_size(x_123);
lean_dec(x_123);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_125 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_124, x_122, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_108 = x_126;
x_109 = x_127;
goto block_117;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_2);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l_Lean_indentExpr(x_4);
x_130 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_133, x_8, x_9, x_10, x_11, x_128);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
return x_134;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_134);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_118);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_139 = l_Lean_indentExpr(x_4);
x_140 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_143, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
block_117:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_array_get_size(x_6);
lean_inc(x_6);
x_111 = l_Array_extract___rarg(x_6, x_106, x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Array_empty___closed__1;
x_114 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_107, x_111, x_111, x_112, x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_6);
lean_dec(x_2);
x_115 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_114, x_114, x_112, x_108);
lean_dec(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
return x_116;
}
}
}
case 2:
{
uint8_t x_149; 
lean_dec(x_7);
x_149 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_150 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = x_6;
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_155, 0, x_1);
lean_closure_set(x_155, 1, x_2);
lean_closure_set(x_155, 2, x_3);
lean_closure_set(x_155, 3, x_154);
lean_closure_set(x_155, 4, x_153);
x_156 = x_155;
x_157 = lean_apply_5(x_156, x_8, x_9, x_10, x_11, x_152);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_159, x_159, x_154, x_151);
lean_dec(x_159);
lean_ctor_set(x_157, 0, x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_157, 0);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_157);
x_163 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_161, x_161, x_154, x_151);
lean_dec(x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_151);
x_165 = !lean_is_exclusive(x_157);
if (x_165 == 0)
{
return x_157;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_157, 0);
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_157);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_150);
if (x_169 == 0)
{
return x_150;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_150, 0);
x_171 = lean_ctor_get(x_150, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_150);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_5);
lean_dec(x_1);
x_173 = lean_ctor_get(x_2, 0);
lean_inc(x_173);
x_174 = lean_array_get_size(x_173);
lean_dec(x_173);
x_175 = lean_ctor_get(x_2, 2);
lean_inc(x_175);
x_186 = lean_nat_add(x_174, x_175);
x_187 = lean_array_get_size(x_6);
x_188 = lean_nat_dec_le(x_187, x_186);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = l_Lean_Expr_Inhabited;
x_190 = lean_array_get(x_189, x_6, x_186);
lean_dec(x_186);
x_191 = lean_ctor_get(x_2, 6);
lean_inc(x_191);
x_192 = lean_array_get_size(x_191);
lean_dec(x_191);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_193 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_192, x_190, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_176 = x_194;
x_177 = x_195;
goto block_185;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec(x_2);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = l_Lean_indentExpr(x_4);
x_198 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_201, x_8, x_9, x_10, x_11, x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
return x_202;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_202);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_186);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_207 = l_Lean_indentExpr(x_4);
x_208 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_211, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
return x_212;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_212);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
block_185:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_array_get_size(x_6);
lean_inc(x_6);
x_179 = l_Array_extract___rarg(x_6, x_174, x_178);
x_180 = lean_unsigned_to_nat(0u);
x_181 = l_Array_empty___closed__1;
x_182 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_175, x_179, x_179, x_180, x_181);
lean_dec(x_179);
lean_dec(x_175);
lean_dec(x_6);
lean_dec(x_2);
x_183 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_182, x_182, x_180, x_176);
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_177);
return x_184;
}
}
}
case 3:
{
uint8_t x_217; 
lean_dec(x_7);
x_217 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_218 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = x_6;
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_223, 0, x_1);
lean_closure_set(x_223, 1, x_2);
lean_closure_set(x_223, 2, x_3);
lean_closure_set(x_223, 3, x_222);
lean_closure_set(x_223, 4, x_221);
x_224 = x_223;
x_225 = lean_apply_5(x_224, x_8, x_9, x_10, x_11, x_220);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_227, x_227, x_222, x_219);
lean_dec(x_227);
lean_ctor_set(x_225, 0, x_228);
return x_225;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_225, 0);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_225);
x_231 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_229, x_229, x_222, x_219);
lean_dec(x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_219);
x_233 = !lean_is_exclusive(x_225);
if (x_233 == 0)
{
return x_225;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_225, 0);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_225);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_218);
if (x_237 == 0)
{
return x_218;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_218, 0);
x_239 = lean_ctor_get(x_218, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_218);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_dec(x_5);
lean_dec(x_1);
x_241 = lean_ctor_get(x_2, 0);
lean_inc(x_241);
x_242 = lean_array_get_size(x_241);
lean_dec(x_241);
x_243 = lean_ctor_get(x_2, 2);
lean_inc(x_243);
x_254 = lean_nat_add(x_242, x_243);
x_255 = lean_array_get_size(x_6);
x_256 = lean_nat_dec_le(x_255, x_254);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_257 = l_Lean_Expr_Inhabited;
x_258 = lean_array_get(x_257, x_6, x_254);
lean_dec(x_254);
x_259 = lean_ctor_get(x_2, 6);
lean_inc(x_259);
x_260 = lean_array_get_size(x_259);
lean_dec(x_259);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_261 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_260, x_258, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_244 = x_262;
x_245 = x_263;
goto block_253;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_6);
lean_dec(x_2);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = l_Lean_indentExpr(x_4);
x_266 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_267 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_269 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_269, x_8, x_9, x_10, x_11, x_264);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
return x_270;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_270, 0);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_270);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_275 = l_Lean_indentExpr(x_4);
x_276 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_277 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_279 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_279, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
return x_280;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_280);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
block_253:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_array_get_size(x_6);
lean_inc(x_6);
x_247 = l_Array_extract___rarg(x_6, x_242, x_246);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l_Array_empty___closed__1;
x_250 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_243, x_247, x_247, x_248, x_249);
lean_dec(x_247);
lean_dec(x_243);
lean_dec(x_6);
lean_dec(x_2);
x_251 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_250, x_250, x_248, x_244);
lean_dec(x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_245);
return x_252;
}
}
}
case 4:
{
uint8_t x_285; 
lean_dec(x_7);
x_285 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_285 == 0)
{
lean_object* x_286; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_286 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = x_6;
x_290 = lean_unsigned_to_nat(0u);
x_291 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_291, 0, x_1);
lean_closure_set(x_291, 1, x_2);
lean_closure_set(x_291, 2, x_3);
lean_closure_set(x_291, 3, x_290);
lean_closure_set(x_291, 4, x_289);
x_292 = x_291;
x_293 = lean_apply_5(x_292, x_8, x_9, x_10, x_11, x_288);
if (lean_obj_tag(x_293) == 0)
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_293, 0);
x_296 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_295, x_295, x_290, x_287);
lean_dec(x_295);
lean_ctor_set(x_293, 0, x_296);
return x_293;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_293, 0);
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_293);
x_299 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_297, x_297, x_290, x_287);
lean_dec(x_297);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
uint8_t x_301; 
lean_dec(x_287);
x_301 = !lean_is_exclusive(x_293);
if (x_301 == 0)
{
return x_293;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_293, 0);
x_303 = lean_ctor_get(x_293, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_293);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_286);
if (x_305 == 0)
{
return x_286;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_286, 0);
x_307 = lean_ctor_get(x_286, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_286);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_5);
lean_dec(x_1);
x_309 = lean_ctor_get(x_2, 0);
lean_inc(x_309);
x_310 = lean_array_get_size(x_309);
lean_dec(x_309);
x_311 = lean_ctor_get(x_2, 2);
lean_inc(x_311);
x_322 = lean_nat_add(x_310, x_311);
x_323 = lean_array_get_size(x_6);
x_324 = lean_nat_dec_le(x_323, x_322);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = l_Lean_Expr_Inhabited;
x_326 = lean_array_get(x_325, x_6, x_322);
lean_dec(x_322);
x_327 = lean_ctor_get(x_2, 6);
lean_inc(x_327);
x_328 = lean_array_get_size(x_327);
lean_dec(x_327);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_329 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_328, x_326, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_312 = x_330;
x_313 = x_331;
goto block_321;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_6);
lean_dec(x_2);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = l_Lean_indentExpr(x_4);
x_334 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_335 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_337 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_337, x_8, x_9, x_10, x_11, x_332);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
return x_338;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_338, 0);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_338);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_322);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_343 = l_Lean_indentExpr(x_4);
x_344 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_345 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_343);
x_346 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_347 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_347, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
return x_348;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_348, 0);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_348);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
block_321:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_314 = lean_array_get_size(x_6);
lean_inc(x_6);
x_315 = l_Array_extract___rarg(x_6, x_310, x_314);
x_316 = lean_unsigned_to_nat(0u);
x_317 = l_Array_empty___closed__1;
x_318 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_311, x_315, x_315, x_316, x_317);
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_6);
lean_dec(x_2);
x_319 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_318, x_318, x_316, x_312);
lean_dec(x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_313);
return x_320;
}
}
}
case 5:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_5, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_5, 1);
lean_inc(x_354);
lean_dec(x_5);
x_355 = lean_array_set(x_6, x_7, x_354);
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_sub(x_7, x_356);
lean_dec(x_7);
x_5 = x_353;
x_6 = x_355;
x_7 = x_357;
goto _start;
}
case 6:
{
uint8_t x_359; 
lean_dec(x_7);
x_359 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_359 == 0)
{
lean_object* x_360; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_360 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = x_6;
x_364 = lean_unsigned_to_nat(0u);
x_365 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_365, 0, x_1);
lean_closure_set(x_365, 1, x_2);
lean_closure_set(x_365, 2, x_3);
lean_closure_set(x_365, 3, x_364);
lean_closure_set(x_365, 4, x_363);
x_366 = x_365;
x_367 = lean_apply_5(x_366, x_8, x_9, x_10, x_11, x_362);
if (lean_obj_tag(x_367) == 0)
{
uint8_t x_368; 
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_369, x_369, x_364, x_361);
lean_dec(x_369);
lean_ctor_set(x_367, 0, x_370);
return x_367;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_367, 0);
x_372 = lean_ctor_get(x_367, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_367);
x_373 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_371, x_371, x_364, x_361);
lean_dec(x_371);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
else
{
uint8_t x_375; 
lean_dec(x_361);
x_375 = !lean_is_exclusive(x_367);
if (x_375 == 0)
{
return x_367;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_367, 0);
x_377 = lean_ctor_get(x_367, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_367);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_379 = !lean_is_exclusive(x_360);
if (x_379 == 0)
{
return x_360;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_360, 0);
x_381 = lean_ctor_get(x_360, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_360);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_5);
lean_dec(x_1);
x_383 = lean_ctor_get(x_2, 0);
lean_inc(x_383);
x_384 = lean_array_get_size(x_383);
lean_dec(x_383);
x_385 = lean_ctor_get(x_2, 2);
lean_inc(x_385);
x_396 = lean_nat_add(x_384, x_385);
x_397 = lean_array_get_size(x_6);
x_398 = lean_nat_dec_le(x_397, x_396);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = l_Lean_Expr_Inhabited;
x_400 = lean_array_get(x_399, x_6, x_396);
lean_dec(x_396);
x_401 = lean_ctor_get(x_2, 6);
lean_inc(x_401);
x_402 = lean_array_get_size(x_401);
lean_dec(x_401);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_403 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_402, x_400, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_386 = x_404;
x_387 = x_405;
goto block_395;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_6);
lean_dec(x_2);
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
lean_dec(x_403);
x_407 = l_Lean_indentExpr(x_4);
x_408 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_409 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
x_410 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_411 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_411, x_8, x_9, x_10, x_11, x_406);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_413 = !lean_is_exclusive(x_412);
if (x_413 == 0)
{
return x_412;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_412, 0);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_412);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
lean_dec(x_396);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_417 = l_Lean_indentExpr(x_4);
x_418 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_419 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_417);
x_420 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_421 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_421, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
return x_422;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_422, 0);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_422);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
block_395:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = lean_array_get_size(x_6);
lean_inc(x_6);
x_389 = l_Array_extract___rarg(x_6, x_384, x_388);
x_390 = lean_unsigned_to_nat(0u);
x_391 = l_Array_empty___closed__1;
x_392 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_385, x_389, x_389, x_390, x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_6);
lean_dec(x_2);
x_393 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_392, x_392, x_390, x_386);
lean_dec(x_392);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_387);
return x_394;
}
}
}
case 7:
{
uint8_t x_427; 
lean_dec(x_7);
x_427 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_428 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = x_6;
x_432 = lean_unsigned_to_nat(0u);
x_433 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_433, 0, x_1);
lean_closure_set(x_433, 1, x_2);
lean_closure_set(x_433, 2, x_3);
lean_closure_set(x_433, 3, x_432);
lean_closure_set(x_433, 4, x_431);
x_434 = x_433;
x_435 = lean_apply_5(x_434, x_8, x_9, x_10, x_11, x_430);
if (lean_obj_tag(x_435) == 0)
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_435);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_435, 0);
x_438 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_437, x_437, x_432, x_429);
lean_dec(x_437);
lean_ctor_set(x_435, 0, x_438);
return x_435;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_439 = lean_ctor_get(x_435, 0);
x_440 = lean_ctor_get(x_435, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_435);
x_441 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_439, x_439, x_432, x_429);
lean_dec(x_439);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
uint8_t x_443; 
lean_dec(x_429);
x_443 = !lean_is_exclusive(x_435);
if (x_443 == 0)
{
return x_435;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_435, 0);
x_445 = lean_ctor_get(x_435, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_435);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_447 = !lean_is_exclusive(x_428);
if (x_447 == 0)
{
return x_428;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_428, 0);
x_449 = lean_ctor_get(x_428, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_428);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
lean_dec(x_5);
lean_dec(x_1);
x_451 = lean_ctor_get(x_2, 0);
lean_inc(x_451);
x_452 = lean_array_get_size(x_451);
lean_dec(x_451);
x_453 = lean_ctor_get(x_2, 2);
lean_inc(x_453);
x_464 = lean_nat_add(x_452, x_453);
x_465 = lean_array_get_size(x_6);
x_466 = lean_nat_dec_le(x_465, x_464);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_467 = l_Lean_Expr_Inhabited;
x_468 = lean_array_get(x_467, x_6, x_464);
lean_dec(x_464);
x_469 = lean_ctor_get(x_2, 6);
lean_inc(x_469);
x_470 = lean_array_get_size(x_469);
lean_dec(x_469);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_471 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_470, x_468, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_454 = x_472;
x_455 = x_473;
goto block_463;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; 
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_6);
lean_dec(x_2);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
lean_dec(x_471);
x_475 = l_Lean_indentExpr(x_4);
x_476 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_477 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_475);
x_478 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_479 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_479, x_8, x_9, x_10, x_11, x_474);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_481 = !lean_is_exclusive(x_480);
if (x_481 == 0)
{
return x_480;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_480, 0);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_480);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
lean_dec(x_464);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_485 = l_Lean_indentExpr(x_4);
x_486 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_487 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_489, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_491 = !lean_is_exclusive(x_490);
if (x_491 == 0)
{
return x_490;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_490, 0);
x_493 = lean_ctor_get(x_490, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_490);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
block_463:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_456 = lean_array_get_size(x_6);
lean_inc(x_6);
x_457 = l_Array_extract___rarg(x_6, x_452, x_456);
x_458 = lean_unsigned_to_nat(0u);
x_459 = l_Array_empty___closed__1;
x_460 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_453, x_457, x_457, x_458, x_459);
lean_dec(x_457);
lean_dec(x_453);
lean_dec(x_6);
lean_dec(x_2);
x_461 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_460, x_460, x_458, x_454);
lean_dec(x_460);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_455);
return x_462;
}
}
}
case 8:
{
uint8_t x_495; 
lean_dec(x_7);
x_495 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_496 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_499 = x_6;
x_500 = lean_unsigned_to_nat(0u);
x_501 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_501, 0, x_1);
lean_closure_set(x_501, 1, x_2);
lean_closure_set(x_501, 2, x_3);
lean_closure_set(x_501, 3, x_500);
lean_closure_set(x_501, 4, x_499);
x_502 = x_501;
x_503 = lean_apply_5(x_502, x_8, x_9, x_10, x_11, x_498);
if (lean_obj_tag(x_503) == 0)
{
uint8_t x_504; 
x_504 = !lean_is_exclusive(x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_503, 0);
x_506 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_505, x_505, x_500, x_497);
lean_dec(x_505);
lean_ctor_set(x_503, 0, x_506);
return x_503;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_503, 0);
x_508 = lean_ctor_get(x_503, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_503);
x_509 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_507, x_507, x_500, x_497);
lean_dec(x_507);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
uint8_t x_511; 
lean_dec(x_497);
x_511 = !lean_is_exclusive(x_503);
if (x_511 == 0)
{
return x_503;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_503, 0);
x_513 = lean_ctor_get(x_503, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_503);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
return x_514;
}
}
}
else
{
uint8_t x_515; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_515 = !lean_is_exclusive(x_496);
if (x_515 == 0)
{
return x_496;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_496, 0);
x_517 = lean_ctor_get(x_496, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_496);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
return x_518;
}
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
lean_dec(x_5);
lean_dec(x_1);
x_519 = lean_ctor_get(x_2, 0);
lean_inc(x_519);
x_520 = lean_array_get_size(x_519);
lean_dec(x_519);
x_521 = lean_ctor_get(x_2, 2);
lean_inc(x_521);
x_532 = lean_nat_add(x_520, x_521);
x_533 = lean_array_get_size(x_6);
x_534 = lean_nat_dec_le(x_533, x_532);
lean_dec(x_533);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_535 = l_Lean_Expr_Inhabited;
x_536 = lean_array_get(x_535, x_6, x_532);
lean_dec(x_532);
x_537 = lean_ctor_get(x_2, 6);
lean_inc(x_537);
x_538 = lean_array_get_size(x_537);
lean_dec(x_537);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_539 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_538, x_536, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_522 = x_540;
x_523 = x_541;
goto block_531;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_2);
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_543 = l_Lean_indentExpr(x_4);
x_544 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_545 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_547 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
x_548 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_547, x_8, x_9, x_10, x_11, x_542);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
return x_548;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_548, 0);
x_551 = lean_ctor_get(x_548, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_548);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
lean_dec(x_532);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_553 = l_Lean_indentExpr(x_4);
x_554 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_555 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_553);
x_556 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_557 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
x_558 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_557, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_559 = !lean_is_exclusive(x_558);
if (x_559 == 0)
{
return x_558;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_558, 0);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_558);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
block_531:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_524 = lean_array_get_size(x_6);
lean_inc(x_6);
x_525 = l_Array_extract___rarg(x_6, x_520, x_524);
x_526 = lean_unsigned_to_nat(0u);
x_527 = l_Array_empty___closed__1;
x_528 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_521, x_525, x_525, x_526, x_527);
lean_dec(x_525);
lean_dec(x_521);
lean_dec(x_6);
lean_dec(x_2);
x_529 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_528, x_528, x_526, x_522);
lean_dec(x_528);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_523);
return x_530;
}
}
}
case 9:
{
uint8_t x_563; 
lean_dec(x_7);
x_563 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_564 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = x_6;
x_568 = lean_unsigned_to_nat(0u);
x_569 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_569, 0, x_1);
lean_closure_set(x_569, 1, x_2);
lean_closure_set(x_569, 2, x_3);
lean_closure_set(x_569, 3, x_568);
lean_closure_set(x_569, 4, x_567);
x_570 = x_569;
x_571 = lean_apply_5(x_570, x_8, x_9, x_10, x_11, x_566);
if (lean_obj_tag(x_571) == 0)
{
uint8_t x_572; 
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_571, 0);
x_574 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_573, x_573, x_568, x_565);
lean_dec(x_573);
lean_ctor_set(x_571, 0, x_574);
return x_571;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_575 = lean_ctor_get(x_571, 0);
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_571);
x_577 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_575, x_575, x_568, x_565);
lean_dec(x_575);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
else
{
uint8_t x_579; 
lean_dec(x_565);
x_579 = !lean_is_exclusive(x_571);
if (x_579 == 0)
{
return x_571;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_571, 0);
x_581 = lean_ctor_get(x_571, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_571);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_564);
if (x_583 == 0)
{
return x_564;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_564, 0);
x_585 = lean_ctor_get(x_564, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_564);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_600; lean_object* x_601; uint8_t x_602; 
lean_dec(x_5);
lean_dec(x_1);
x_587 = lean_ctor_get(x_2, 0);
lean_inc(x_587);
x_588 = lean_array_get_size(x_587);
lean_dec(x_587);
x_589 = lean_ctor_get(x_2, 2);
lean_inc(x_589);
x_600 = lean_nat_add(x_588, x_589);
x_601 = lean_array_get_size(x_6);
x_602 = lean_nat_dec_le(x_601, x_600);
lean_dec(x_601);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_603 = l_Lean_Expr_Inhabited;
x_604 = lean_array_get(x_603, x_6, x_600);
lean_dec(x_600);
x_605 = lean_ctor_get(x_2, 6);
lean_inc(x_605);
x_606 = lean_array_get_size(x_605);
lean_dec(x_605);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_607 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_606, x_604, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_590 = x_608;
x_591 = x_609;
goto block_599;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_6);
lean_dec(x_2);
x_610 = lean_ctor_get(x_607, 1);
lean_inc(x_610);
lean_dec(x_607);
x_611 = l_Lean_indentExpr(x_4);
x_612 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_613 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
x_614 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_615 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
x_616 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_615, x_8, x_9, x_10, x_11, x_610);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_617 = !lean_is_exclusive(x_616);
if (x_617 == 0)
{
return x_616;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_616, 0);
x_619 = lean_ctor_get(x_616, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_616);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
lean_dec(x_600);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_621 = l_Lean_indentExpr(x_4);
x_622 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_623 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_621);
x_624 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_625 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
x_626 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_625, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
return x_626;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_626);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
block_599:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_592 = lean_array_get_size(x_6);
lean_inc(x_6);
x_593 = l_Array_extract___rarg(x_6, x_588, x_592);
x_594 = lean_unsigned_to_nat(0u);
x_595 = l_Array_empty___closed__1;
x_596 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_589, x_593, x_593, x_594, x_595);
lean_dec(x_593);
lean_dec(x_589);
lean_dec(x_6);
lean_dec(x_2);
x_597 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_596, x_596, x_594, x_590);
lean_dec(x_596);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_591);
return x_598;
}
}
}
case 10:
{
uint8_t x_631; 
lean_dec(x_7);
x_631 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_632 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = x_6;
x_636 = lean_unsigned_to_nat(0u);
x_637 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_637, 0, x_1);
lean_closure_set(x_637, 1, x_2);
lean_closure_set(x_637, 2, x_3);
lean_closure_set(x_637, 3, x_636);
lean_closure_set(x_637, 4, x_635);
x_638 = x_637;
x_639 = lean_apply_5(x_638, x_8, x_9, x_10, x_11, x_634);
if (lean_obj_tag(x_639) == 0)
{
uint8_t x_640; 
x_640 = !lean_is_exclusive(x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; 
x_641 = lean_ctor_get(x_639, 0);
x_642 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_641, x_641, x_636, x_633);
lean_dec(x_641);
lean_ctor_set(x_639, 0, x_642);
return x_639;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_643 = lean_ctor_get(x_639, 0);
x_644 = lean_ctor_get(x_639, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_639);
x_645 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_643, x_643, x_636, x_633);
lean_dec(x_643);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
uint8_t x_647; 
lean_dec(x_633);
x_647 = !lean_is_exclusive(x_639);
if (x_647 == 0)
{
return x_639;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_639, 0);
x_649 = lean_ctor_get(x_639, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_639);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
else
{
uint8_t x_651; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_651 = !lean_is_exclusive(x_632);
if (x_651 == 0)
{
return x_632;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_632, 0);
x_653 = lean_ctor_get(x_632, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_632);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
lean_dec(x_5);
lean_dec(x_1);
x_655 = lean_ctor_get(x_2, 0);
lean_inc(x_655);
x_656 = lean_array_get_size(x_655);
lean_dec(x_655);
x_657 = lean_ctor_get(x_2, 2);
lean_inc(x_657);
x_668 = lean_nat_add(x_656, x_657);
x_669 = lean_array_get_size(x_6);
x_670 = lean_nat_dec_le(x_669, x_668);
lean_dec(x_669);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_671 = l_Lean_Expr_Inhabited;
x_672 = lean_array_get(x_671, x_6, x_668);
lean_dec(x_668);
x_673 = lean_ctor_get(x_2, 6);
lean_inc(x_673);
x_674 = lean_array_get_size(x_673);
lean_dec(x_673);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_675 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_674, x_672, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_658 = x_676;
x_659 = x_677;
goto block_667;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_2);
x_678 = lean_ctor_get(x_675, 1);
lean_inc(x_678);
lean_dec(x_675);
x_679 = l_Lean_indentExpr(x_4);
x_680 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_681 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_679);
x_682 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_683 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
x_684 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_683, x_8, x_9, x_10, x_11, x_678);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_685 = !lean_is_exclusive(x_684);
if (x_685 == 0)
{
return x_684;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_684, 0);
x_687 = lean_ctor_get(x_684, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_684);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
return x_688;
}
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
lean_dec(x_668);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_689 = l_Lean_indentExpr(x_4);
x_690 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_691 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_692 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_693 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
x_694 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_693, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_695 = !lean_is_exclusive(x_694);
if (x_695 == 0)
{
return x_694;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_694, 0);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_inc(x_696);
lean_dec(x_694);
x_698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
return x_698;
}
}
block_667:
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_660 = lean_array_get_size(x_6);
lean_inc(x_6);
x_661 = l_Array_extract___rarg(x_6, x_656, x_660);
x_662 = lean_unsigned_to_nat(0u);
x_663 = l_Array_empty___closed__1;
x_664 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_657, x_661, x_661, x_662, x_663);
lean_dec(x_661);
lean_dec(x_657);
lean_dec(x_6);
lean_dec(x_2);
x_665 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_664, x_664, x_662, x_658);
lean_dec(x_664);
x_666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_659);
return x_666;
}
}
}
case 11:
{
uint8_t x_699; 
lean_dec(x_7);
x_699 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_699 == 0)
{
lean_object* x_700; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_700 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = x_6;
x_704 = lean_unsigned_to_nat(0u);
x_705 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_705, 0, x_1);
lean_closure_set(x_705, 1, x_2);
lean_closure_set(x_705, 2, x_3);
lean_closure_set(x_705, 3, x_704);
lean_closure_set(x_705, 4, x_703);
x_706 = x_705;
x_707 = lean_apply_5(x_706, x_8, x_9, x_10, x_11, x_702);
if (lean_obj_tag(x_707) == 0)
{
uint8_t x_708; 
x_708 = !lean_is_exclusive(x_707);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_707, 0);
x_710 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_709, x_709, x_704, x_701);
lean_dec(x_709);
lean_ctor_set(x_707, 0, x_710);
return x_707;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_711 = lean_ctor_get(x_707, 0);
x_712 = lean_ctor_get(x_707, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_707);
x_713 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_711, x_711, x_704, x_701);
lean_dec(x_711);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_712);
return x_714;
}
}
else
{
uint8_t x_715; 
lean_dec(x_701);
x_715 = !lean_is_exclusive(x_707);
if (x_715 == 0)
{
return x_707;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_707, 0);
x_717 = lean_ctor_get(x_707, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_707);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
}
else
{
uint8_t x_719; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_719 = !lean_is_exclusive(x_700);
if (x_719 == 0)
{
return x_700;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_720 = lean_ctor_get(x_700, 0);
x_721 = lean_ctor_get(x_700, 1);
lean_inc(x_721);
lean_inc(x_720);
lean_dec(x_700);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
return x_722;
}
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_736; lean_object* x_737; uint8_t x_738; 
lean_dec(x_5);
lean_dec(x_1);
x_723 = lean_ctor_get(x_2, 0);
lean_inc(x_723);
x_724 = lean_array_get_size(x_723);
lean_dec(x_723);
x_725 = lean_ctor_get(x_2, 2);
lean_inc(x_725);
x_736 = lean_nat_add(x_724, x_725);
x_737 = lean_array_get_size(x_6);
x_738 = lean_nat_dec_le(x_737, x_736);
lean_dec(x_737);
if (x_738 == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_739 = l_Lean_Expr_Inhabited;
x_740 = lean_array_get(x_739, x_6, x_736);
lean_dec(x_736);
x_741 = lean_ctor_get(x_2, 6);
lean_inc(x_741);
x_742 = lean_array_get_size(x_741);
lean_dec(x_741);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_743 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_742, x_740, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_726 = x_744;
x_727 = x_745;
goto block_735;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
lean_dec(x_725);
lean_dec(x_724);
lean_dec(x_6);
lean_dec(x_2);
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
lean_dec(x_743);
x_747 = l_Lean_indentExpr(x_4);
x_748 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_749 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_747);
x_750 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_751 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
x_752 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_751, x_8, x_9, x_10, x_11, x_746);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_753 = !lean_is_exclusive(x_752);
if (x_753 == 0)
{
return x_752;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_752, 0);
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_752);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; 
lean_dec(x_736);
lean_dec(x_725);
lean_dec(x_724);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_757 = l_Lean_indentExpr(x_4);
x_758 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_759 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
x_760 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_761 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
x_762 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_761, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_763 = !lean_is_exclusive(x_762);
if (x_763 == 0)
{
return x_762;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_762, 0);
x_765 = lean_ctor_get(x_762, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_762);
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
return x_766;
}
}
block_735:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_728 = lean_array_get_size(x_6);
lean_inc(x_6);
x_729 = l_Array_extract___rarg(x_6, x_724, x_728);
x_730 = lean_unsigned_to_nat(0u);
x_731 = l_Array_empty___closed__1;
x_732 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_725, x_729, x_729, x_730, x_731);
lean_dec(x_729);
lean_dec(x_725);
lean_dec(x_6);
lean_dec(x_2);
x_733 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_732, x_732, x_730, x_726);
lean_dec(x_732);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_727);
return x_734;
}
}
}
default: 
{
uint8_t x_767; 
lean_dec(x_7);
x_767 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_767 == 0)
{
lean_object* x_768; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_768 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
x_771 = x_6;
x_772 = lean_unsigned_to_nat(0u);
x_773 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_773, 0, x_1);
lean_closure_set(x_773, 1, x_2);
lean_closure_set(x_773, 2, x_3);
lean_closure_set(x_773, 3, x_772);
lean_closure_set(x_773, 4, x_771);
x_774 = x_773;
x_775 = lean_apply_5(x_774, x_8, x_9, x_10, x_11, x_770);
if (lean_obj_tag(x_775) == 0)
{
uint8_t x_776; 
x_776 = !lean_is_exclusive(x_775);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; 
x_777 = lean_ctor_get(x_775, 0);
x_778 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_777, x_777, x_772, x_769);
lean_dec(x_777);
lean_ctor_set(x_775, 0, x_778);
return x_775;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_779 = lean_ctor_get(x_775, 0);
x_780 = lean_ctor_get(x_775, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_775);
x_781 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_779, x_779, x_772, x_769);
lean_dec(x_779);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
else
{
uint8_t x_783; 
lean_dec(x_769);
x_783 = !lean_is_exclusive(x_775);
if (x_783 == 0)
{
return x_775;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_775, 0);
x_785 = lean_ctor_get(x_775, 1);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_775);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
return x_786;
}
}
}
else
{
uint8_t x_787; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_787 = !lean_is_exclusive(x_768);
if (x_787 == 0)
{
return x_768;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_768, 0);
x_789 = lean_ctor_get(x_768, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_768);
x_790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_790, 0, x_788);
lean_ctor_set(x_790, 1, x_789);
return x_790;
}
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_804; lean_object* x_805; uint8_t x_806; 
lean_dec(x_5);
lean_dec(x_1);
x_791 = lean_ctor_get(x_2, 0);
lean_inc(x_791);
x_792 = lean_array_get_size(x_791);
lean_dec(x_791);
x_793 = lean_ctor_get(x_2, 2);
lean_inc(x_793);
x_804 = lean_nat_add(x_792, x_793);
x_805 = lean_array_get_size(x_6);
x_806 = lean_nat_dec_le(x_805, x_804);
lean_dec(x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_807 = l_Lean_Expr_Inhabited;
x_808 = lean_array_get(x_807, x_6, x_804);
lean_dec(x_804);
x_809 = lean_ctor_get(x_2, 6);
lean_inc(x_809);
x_810 = lean_array_get_size(x_809);
lean_dec(x_809);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_811 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_810, x_808, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_794 = x_812;
x_795 = x_813;
goto block_803;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; uint8_t x_821; 
lean_dec(x_793);
lean_dec(x_792);
lean_dec(x_6);
lean_dec(x_2);
x_814 = lean_ctor_get(x_811, 1);
lean_inc(x_814);
lean_dec(x_811);
x_815 = l_Lean_indentExpr(x_4);
x_816 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_817 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_815);
x_818 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_819 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
x_820 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_819, x_8, x_9, x_10, x_11, x_814);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_821 = !lean_is_exclusive(x_820);
if (x_821 == 0)
{
return x_820;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_820, 0);
x_823 = lean_ctor_get(x_820, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_820);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; 
lean_dec(x_804);
lean_dec(x_793);
lean_dec(x_792);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_825 = l_Lean_indentExpr(x_4);
x_826 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_827 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_825);
x_828 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_829 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_829, 0, x_827);
lean_ctor_set(x_829, 1, x_828);
x_830 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_829, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_831 = !lean_is_exclusive(x_830);
if (x_831 == 0)
{
return x_830;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_832 = lean_ctor_get(x_830, 0);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_inc(x_832);
lean_dec(x_830);
x_834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_834, 0, x_832);
lean_ctor_set(x_834, 1, x_833);
return x_834;
}
}
block_803:
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_796 = lean_array_get_size(x_6);
lean_inc(x_6);
x_797 = l_Array_extract___rarg(x_6, x_792, x_796);
x_798 = lean_unsigned_to_nat(0u);
x_799 = l_Array_empty___closed__1;
x_800 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_2, x_6, x_793, x_797, x_797, x_798, x_799);
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_6);
lean_dec(x_2);
x_801 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_800, x_800, x_798, x_794);
lean_dec(x_800);
x_802 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_795);
return x_802;
}
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_5;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_5, x_4, x_16);
x_18 = x_15;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_17, x_4, x_24);
lean_dec(x_4);
x_4 = x_23;
x_5 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_5, x_6);
x_11 = lean_nat_dec_eq(x_3, x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
if (x_11 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 3);
x_15 = l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_14, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_push(x_7, x_10);
x_6 = x_13;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_10);
x_6 = x_13;
goto _start;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
x_6 = x_13;
goto _start;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = x_6;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_17);
x_20 = x_19;
x_21 = lean_apply_5(x_20, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_23, x_23, x_18, x_15);
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
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_25, x_25, x_18, x_15);
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
lean_dec(x_15);
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
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_array_get_size(x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_50 = lean_nat_add(x_38, x_39);
x_51 = lean_array_get_size(x_6);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_Expr_Inhabited;
x_54 = lean_array_get(x_53, x_6, x_50);
lean_dec(x_50);
x_55 = lean_ctor_get(x_2, 6);
lean_inc(x_55);
x_56 = lean_array_get_size(x_55);
lean_dec(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_56, x_54, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_40 = x_58;
x_41 = x_59;
goto block_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_2);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_indentExpr(x_4);
x_62 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_65, x_8, x_9, x_10, x_11, x_60);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_71 = l_Lean_indentExpr(x_4);
x_72 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_75, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
block_49:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_array_get_size(x_6);
lean_inc(x_6);
x_43 = l_Array_extract___rarg(x_6, x_38, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_empty___closed__1;
x_46 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_39, x_43, x_43, x_44, x_45);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_2);
x_47 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_46, x_46, x_44, x_40);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
}
}
case 1:
{
uint8_t x_81; 
lean_dec(x_7);
x_81 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = x_6;
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_87, 0, x_1);
lean_closure_set(x_87, 1, x_2);
lean_closure_set(x_87, 2, x_3);
lean_closure_set(x_87, 3, x_86);
lean_closure_set(x_87, 4, x_85);
x_88 = x_87;
x_89 = lean_apply_5(x_88, x_8, x_9, x_10, x_11, x_84);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_91, x_91, x_86, x_83);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_93, x_93, x_86, x_83);
lean_dec(x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_83);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
return x_82;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_82, 0);
x_103 = lean_ctor_get(x_82, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_82);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_5);
lean_dec(x_1);
x_105 = lean_ctor_get(x_2, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
x_118 = lean_nat_add(x_106, x_107);
x_119 = lean_array_get_size(x_6);
x_120 = lean_nat_dec_le(x_119, x_118);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Lean_Expr_Inhabited;
x_122 = lean_array_get(x_121, x_6, x_118);
lean_dec(x_118);
x_123 = lean_ctor_get(x_2, 6);
lean_inc(x_123);
x_124 = lean_array_get_size(x_123);
lean_dec(x_123);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_125 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_124, x_122, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_108 = x_126;
x_109 = x_127;
goto block_117;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_2);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l_Lean_indentExpr(x_4);
x_130 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_133, x_8, x_9, x_10, x_11, x_128);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
return x_134;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_134);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_118);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_139 = l_Lean_indentExpr(x_4);
x_140 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_143, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
block_117:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_array_get_size(x_6);
lean_inc(x_6);
x_111 = l_Array_extract___rarg(x_6, x_106, x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Array_empty___closed__1;
x_114 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_107, x_111, x_111, x_112, x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_6);
lean_dec(x_2);
x_115 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_114, x_114, x_112, x_108);
lean_dec(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
return x_116;
}
}
}
case 2:
{
uint8_t x_149; 
lean_dec(x_7);
x_149 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_150 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = x_6;
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_155, 0, x_1);
lean_closure_set(x_155, 1, x_2);
lean_closure_set(x_155, 2, x_3);
lean_closure_set(x_155, 3, x_154);
lean_closure_set(x_155, 4, x_153);
x_156 = x_155;
x_157 = lean_apply_5(x_156, x_8, x_9, x_10, x_11, x_152);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_159, x_159, x_154, x_151);
lean_dec(x_159);
lean_ctor_set(x_157, 0, x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_157, 0);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_157);
x_163 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_161, x_161, x_154, x_151);
lean_dec(x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_151);
x_165 = !lean_is_exclusive(x_157);
if (x_165 == 0)
{
return x_157;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_157, 0);
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_157);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_150);
if (x_169 == 0)
{
return x_150;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_150, 0);
x_171 = lean_ctor_get(x_150, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_150);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_5);
lean_dec(x_1);
x_173 = lean_ctor_get(x_2, 0);
lean_inc(x_173);
x_174 = lean_array_get_size(x_173);
lean_dec(x_173);
x_175 = lean_ctor_get(x_2, 2);
lean_inc(x_175);
x_186 = lean_nat_add(x_174, x_175);
x_187 = lean_array_get_size(x_6);
x_188 = lean_nat_dec_le(x_187, x_186);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = l_Lean_Expr_Inhabited;
x_190 = lean_array_get(x_189, x_6, x_186);
lean_dec(x_186);
x_191 = lean_ctor_get(x_2, 6);
lean_inc(x_191);
x_192 = lean_array_get_size(x_191);
lean_dec(x_191);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_193 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_192, x_190, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_176 = x_194;
x_177 = x_195;
goto block_185;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec(x_2);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = l_Lean_indentExpr(x_4);
x_198 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_201, x_8, x_9, x_10, x_11, x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
return x_202;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_202);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_186);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_207 = l_Lean_indentExpr(x_4);
x_208 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_211, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
return x_212;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_212);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
block_185:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_array_get_size(x_6);
lean_inc(x_6);
x_179 = l_Array_extract___rarg(x_6, x_174, x_178);
x_180 = lean_unsigned_to_nat(0u);
x_181 = l_Array_empty___closed__1;
x_182 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_175, x_179, x_179, x_180, x_181);
lean_dec(x_179);
lean_dec(x_175);
lean_dec(x_6);
lean_dec(x_2);
x_183 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_182, x_182, x_180, x_176);
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_177);
return x_184;
}
}
}
case 3:
{
uint8_t x_217; 
lean_dec(x_7);
x_217 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_218 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = x_6;
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_223, 0, x_1);
lean_closure_set(x_223, 1, x_2);
lean_closure_set(x_223, 2, x_3);
lean_closure_set(x_223, 3, x_222);
lean_closure_set(x_223, 4, x_221);
x_224 = x_223;
x_225 = lean_apply_5(x_224, x_8, x_9, x_10, x_11, x_220);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_227, x_227, x_222, x_219);
lean_dec(x_227);
lean_ctor_set(x_225, 0, x_228);
return x_225;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_225, 0);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_225);
x_231 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_229, x_229, x_222, x_219);
lean_dec(x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_219);
x_233 = !lean_is_exclusive(x_225);
if (x_233 == 0)
{
return x_225;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_225, 0);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_225);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_218);
if (x_237 == 0)
{
return x_218;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_218, 0);
x_239 = lean_ctor_get(x_218, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_218);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_dec(x_5);
lean_dec(x_1);
x_241 = lean_ctor_get(x_2, 0);
lean_inc(x_241);
x_242 = lean_array_get_size(x_241);
lean_dec(x_241);
x_243 = lean_ctor_get(x_2, 2);
lean_inc(x_243);
x_254 = lean_nat_add(x_242, x_243);
x_255 = lean_array_get_size(x_6);
x_256 = lean_nat_dec_le(x_255, x_254);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_257 = l_Lean_Expr_Inhabited;
x_258 = lean_array_get(x_257, x_6, x_254);
lean_dec(x_254);
x_259 = lean_ctor_get(x_2, 6);
lean_inc(x_259);
x_260 = lean_array_get_size(x_259);
lean_dec(x_259);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_261 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_260, x_258, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_244 = x_262;
x_245 = x_263;
goto block_253;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_6);
lean_dec(x_2);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = l_Lean_indentExpr(x_4);
x_266 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_267 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_269 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_269, x_8, x_9, x_10, x_11, x_264);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
return x_270;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_270, 0);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_270);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_275 = l_Lean_indentExpr(x_4);
x_276 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_277 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_279 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_279, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
return x_280;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_280);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
block_253:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_array_get_size(x_6);
lean_inc(x_6);
x_247 = l_Array_extract___rarg(x_6, x_242, x_246);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l_Array_empty___closed__1;
x_250 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_243, x_247, x_247, x_248, x_249);
lean_dec(x_247);
lean_dec(x_243);
lean_dec(x_6);
lean_dec(x_2);
x_251 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_250, x_250, x_248, x_244);
lean_dec(x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_245);
return x_252;
}
}
}
case 4:
{
uint8_t x_285; 
lean_dec(x_7);
x_285 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_285 == 0)
{
lean_object* x_286; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_286 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = x_6;
x_290 = lean_unsigned_to_nat(0u);
x_291 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_291, 0, x_1);
lean_closure_set(x_291, 1, x_2);
lean_closure_set(x_291, 2, x_3);
lean_closure_set(x_291, 3, x_290);
lean_closure_set(x_291, 4, x_289);
x_292 = x_291;
x_293 = lean_apply_5(x_292, x_8, x_9, x_10, x_11, x_288);
if (lean_obj_tag(x_293) == 0)
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_293, 0);
x_296 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_295, x_295, x_290, x_287);
lean_dec(x_295);
lean_ctor_set(x_293, 0, x_296);
return x_293;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_293, 0);
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_293);
x_299 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_297, x_297, x_290, x_287);
lean_dec(x_297);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
uint8_t x_301; 
lean_dec(x_287);
x_301 = !lean_is_exclusive(x_293);
if (x_301 == 0)
{
return x_293;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_293, 0);
x_303 = lean_ctor_get(x_293, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_293);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_286);
if (x_305 == 0)
{
return x_286;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_286, 0);
x_307 = lean_ctor_get(x_286, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_286);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_5);
lean_dec(x_1);
x_309 = lean_ctor_get(x_2, 0);
lean_inc(x_309);
x_310 = lean_array_get_size(x_309);
lean_dec(x_309);
x_311 = lean_ctor_get(x_2, 2);
lean_inc(x_311);
x_322 = lean_nat_add(x_310, x_311);
x_323 = lean_array_get_size(x_6);
x_324 = lean_nat_dec_le(x_323, x_322);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = l_Lean_Expr_Inhabited;
x_326 = lean_array_get(x_325, x_6, x_322);
lean_dec(x_322);
x_327 = lean_ctor_get(x_2, 6);
lean_inc(x_327);
x_328 = lean_array_get_size(x_327);
lean_dec(x_327);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_329 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_328, x_326, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_312 = x_330;
x_313 = x_331;
goto block_321;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_6);
lean_dec(x_2);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = l_Lean_indentExpr(x_4);
x_334 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_335 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_337 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_337, x_8, x_9, x_10, x_11, x_332);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
return x_338;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_338, 0);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_338);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_322);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_343 = l_Lean_indentExpr(x_4);
x_344 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_345 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_343);
x_346 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_347 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_347, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
return x_348;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_348, 0);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_348);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
block_321:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_314 = lean_array_get_size(x_6);
lean_inc(x_6);
x_315 = l_Array_extract___rarg(x_6, x_310, x_314);
x_316 = lean_unsigned_to_nat(0u);
x_317 = l_Array_empty___closed__1;
x_318 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_311, x_315, x_315, x_316, x_317);
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_6);
lean_dec(x_2);
x_319 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_318, x_318, x_316, x_312);
lean_dec(x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_313);
return x_320;
}
}
}
case 5:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_5, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_5, 1);
lean_inc(x_354);
lean_dec(x_5);
x_355 = lean_array_set(x_6, x_7, x_354);
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_sub(x_7, x_356);
lean_dec(x_7);
x_5 = x_353;
x_6 = x_355;
x_7 = x_357;
goto _start;
}
case 6:
{
uint8_t x_359; 
lean_dec(x_7);
x_359 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_359 == 0)
{
lean_object* x_360; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_360 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = x_6;
x_364 = lean_unsigned_to_nat(0u);
x_365 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_365, 0, x_1);
lean_closure_set(x_365, 1, x_2);
lean_closure_set(x_365, 2, x_3);
lean_closure_set(x_365, 3, x_364);
lean_closure_set(x_365, 4, x_363);
x_366 = x_365;
x_367 = lean_apply_5(x_366, x_8, x_9, x_10, x_11, x_362);
if (lean_obj_tag(x_367) == 0)
{
uint8_t x_368; 
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_369, x_369, x_364, x_361);
lean_dec(x_369);
lean_ctor_set(x_367, 0, x_370);
return x_367;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_367, 0);
x_372 = lean_ctor_get(x_367, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_367);
x_373 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_371, x_371, x_364, x_361);
lean_dec(x_371);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
else
{
uint8_t x_375; 
lean_dec(x_361);
x_375 = !lean_is_exclusive(x_367);
if (x_375 == 0)
{
return x_367;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_367, 0);
x_377 = lean_ctor_get(x_367, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_367);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_379 = !lean_is_exclusive(x_360);
if (x_379 == 0)
{
return x_360;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_360, 0);
x_381 = lean_ctor_get(x_360, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_360);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_5);
lean_dec(x_1);
x_383 = lean_ctor_get(x_2, 0);
lean_inc(x_383);
x_384 = lean_array_get_size(x_383);
lean_dec(x_383);
x_385 = lean_ctor_get(x_2, 2);
lean_inc(x_385);
x_396 = lean_nat_add(x_384, x_385);
x_397 = lean_array_get_size(x_6);
x_398 = lean_nat_dec_le(x_397, x_396);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = l_Lean_Expr_Inhabited;
x_400 = lean_array_get(x_399, x_6, x_396);
lean_dec(x_396);
x_401 = lean_ctor_get(x_2, 6);
lean_inc(x_401);
x_402 = lean_array_get_size(x_401);
lean_dec(x_401);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_403 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_402, x_400, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_386 = x_404;
x_387 = x_405;
goto block_395;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_6);
lean_dec(x_2);
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
lean_dec(x_403);
x_407 = l_Lean_indentExpr(x_4);
x_408 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_409 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
x_410 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_411 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_411, x_8, x_9, x_10, x_11, x_406);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_413 = !lean_is_exclusive(x_412);
if (x_413 == 0)
{
return x_412;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_412, 0);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_412);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
lean_dec(x_396);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_417 = l_Lean_indentExpr(x_4);
x_418 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_419 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_417);
x_420 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_421 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_421, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
return x_422;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_422, 0);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_422);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
block_395:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = lean_array_get_size(x_6);
lean_inc(x_6);
x_389 = l_Array_extract___rarg(x_6, x_384, x_388);
x_390 = lean_unsigned_to_nat(0u);
x_391 = l_Array_empty___closed__1;
x_392 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_385, x_389, x_389, x_390, x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_6);
lean_dec(x_2);
x_393 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_392, x_392, x_390, x_386);
lean_dec(x_392);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_387);
return x_394;
}
}
}
case 7:
{
uint8_t x_427; 
lean_dec(x_7);
x_427 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_428 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = x_6;
x_432 = lean_unsigned_to_nat(0u);
x_433 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_433, 0, x_1);
lean_closure_set(x_433, 1, x_2);
lean_closure_set(x_433, 2, x_3);
lean_closure_set(x_433, 3, x_432);
lean_closure_set(x_433, 4, x_431);
x_434 = x_433;
x_435 = lean_apply_5(x_434, x_8, x_9, x_10, x_11, x_430);
if (lean_obj_tag(x_435) == 0)
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_435);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_435, 0);
x_438 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_437, x_437, x_432, x_429);
lean_dec(x_437);
lean_ctor_set(x_435, 0, x_438);
return x_435;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_439 = lean_ctor_get(x_435, 0);
x_440 = lean_ctor_get(x_435, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_435);
x_441 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_439, x_439, x_432, x_429);
lean_dec(x_439);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
uint8_t x_443; 
lean_dec(x_429);
x_443 = !lean_is_exclusive(x_435);
if (x_443 == 0)
{
return x_435;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_435, 0);
x_445 = lean_ctor_get(x_435, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_435);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_447 = !lean_is_exclusive(x_428);
if (x_447 == 0)
{
return x_428;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_428, 0);
x_449 = lean_ctor_get(x_428, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_428);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
lean_dec(x_5);
lean_dec(x_1);
x_451 = lean_ctor_get(x_2, 0);
lean_inc(x_451);
x_452 = lean_array_get_size(x_451);
lean_dec(x_451);
x_453 = lean_ctor_get(x_2, 2);
lean_inc(x_453);
x_464 = lean_nat_add(x_452, x_453);
x_465 = lean_array_get_size(x_6);
x_466 = lean_nat_dec_le(x_465, x_464);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_467 = l_Lean_Expr_Inhabited;
x_468 = lean_array_get(x_467, x_6, x_464);
lean_dec(x_464);
x_469 = lean_ctor_get(x_2, 6);
lean_inc(x_469);
x_470 = lean_array_get_size(x_469);
lean_dec(x_469);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_471 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_470, x_468, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_454 = x_472;
x_455 = x_473;
goto block_463;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; 
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_6);
lean_dec(x_2);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
lean_dec(x_471);
x_475 = l_Lean_indentExpr(x_4);
x_476 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_477 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_475);
x_478 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_479 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_479, x_8, x_9, x_10, x_11, x_474);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_481 = !lean_is_exclusive(x_480);
if (x_481 == 0)
{
return x_480;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_480, 0);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_480);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
lean_dec(x_464);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_485 = l_Lean_indentExpr(x_4);
x_486 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_487 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_489, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_491 = !lean_is_exclusive(x_490);
if (x_491 == 0)
{
return x_490;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_490, 0);
x_493 = lean_ctor_get(x_490, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_490);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
block_463:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_456 = lean_array_get_size(x_6);
lean_inc(x_6);
x_457 = l_Array_extract___rarg(x_6, x_452, x_456);
x_458 = lean_unsigned_to_nat(0u);
x_459 = l_Array_empty___closed__1;
x_460 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_453, x_457, x_457, x_458, x_459);
lean_dec(x_457);
lean_dec(x_453);
lean_dec(x_6);
lean_dec(x_2);
x_461 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_460, x_460, x_458, x_454);
lean_dec(x_460);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_455);
return x_462;
}
}
}
case 8:
{
uint8_t x_495; 
lean_dec(x_7);
x_495 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_496 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_499 = x_6;
x_500 = lean_unsigned_to_nat(0u);
x_501 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_501, 0, x_1);
lean_closure_set(x_501, 1, x_2);
lean_closure_set(x_501, 2, x_3);
lean_closure_set(x_501, 3, x_500);
lean_closure_set(x_501, 4, x_499);
x_502 = x_501;
x_503 = lean_apply_5(x_502, x_8, x_9, x_10, x_11, x_498);
if (lean_obj_tag(x_503) == 0)
{
uint8_t x_504; 
x_504 = !lean_is_exclusive(x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_503, 0);
x_506 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_505, x_505, x_500, x_497);
lean_dec(x_505);
lean_ctor_set(x_503, 0, x_506);
return x_503;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_503, 0);
x_508 = lean_ctor_get(x_503, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_503);
x_509 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_507, x_507, x_500, x_497);
lean_dec(x_507);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
uint8_t x_511; 
lean_dec(x_497);
x_511 = !lean_is_exclusive(x_503);
if (x_511 == 0)
{
return x_503;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_503, 0);
x_513 = lean_ctor_get(x_503, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_503);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
return x_514;
}
}
}
else
{
uint8_t x_515; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_515 = !lean_is_exclusive(x_496);
if (x_515 == 0)
{
return x_496;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_496, 0);
x_517 = lean_ctor_get(x_496, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_496);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
return x_518;
}
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
lean_dec(x_5);
lean_dec(x_1);
x_519 = lean_ctor_get(x_2, 0);
lean_inc(x_519);
x_520 = lean_array_get_size(x_519);
lean_dec(x_519);
x_521 = lean_ctor_get(x_2, 2);
lean_inc(x_521);
x_532 = lean_nat_add(x_520, x_521);
x_533 = lean_array_get_size(x_6);
x_534 = lean_nat_dec_le(x_533, x_532);
lean_dec(x_533);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_535 = l_Lean_Expr_Inhabited;
x_536 = lean_array_get(x_535, x_6, x_532);
lean_dec(x_532);
x_537 = lean_ctor_get(x_2, 6);
lean_inc(x_537);
x_538 = lean_array_get_size(x_537);
lean_dec(x_537);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_539 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_538, x_536, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_522 = x_540;
x_523 = x_541;
goto block_531;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_2);
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_543 = l_Lean_indentExpr(x_4);
x_544 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_545 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_547 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
x_548 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_547, x_8, x_9, x_10, x_11, x_542);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
return x_548;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_548, 0);
x_551 = lean_ctor_get(x_548, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_548);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
lean_dec(x_532);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_553 = l_Lean_indentExpr(x_4);
x_554 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_555 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_553);
x_556 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_557 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
x_558 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_557, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_559 = !lean_is_exclusive(x_558);
if (x_559 == 0)
{
return x_558;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_558, 0);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_558);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
block_531:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_524 = lean_array_get_size(x_6);
lean_inc(x_6);
x_525 = l_Array_extract___rarg(x_6, x_520, x_524);
x_526 = lean_unsigned_to_nat(0u);
x_527 = l_Array_empty___closed__1;
x_528 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_521, x_525, x_525, x_526, x_527);
lean_dec(x_525);
lean_dec(x_521);
lean_dec(x_6);
lean_dec(x_2);
x_529 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_528, x_528, x_526, x_522);
lean_dec(x_528);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_523);
return x_530;
}
}
}
case 9:
{
uint8_t x_563; 
lean_dec(x_7);
x_563 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_564 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = x_6;
x_568 = lean_unsigned_to_nat(0u);
x_569 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_569, 0, x_1);
lean_closure_set(x_569, 1, x_2);
lean_closure_set(x_569, 2, x_3);
lean_closure_set(x_569, 3, x_568);
lean_closure_set(x_569, 4, x_567);
x_570 = x_569;
x_571 = lean_apply_5(x_570, x_8, x_9, x_10, x_11, x_566);
if (lean_obj_tag(x_571) == 0)
{
uint8_t x_572; 
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_571, 0);
x_574 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_573, x_573, x_568, x_565);
lean_dec(x_573);
lean_ctor_set(x_571, 0, x_574);
return x_571;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_575 = lean_ctor_get(x_571, 0);
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_571);
x_577 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_575, x_575, x_568, x_565);
lean_dec(x_575);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
else
{
uint8_t x_579; 
lean_dec(x_565);
x_579 = !lean_is_exclusive(x_571);
if (x_579 == 0)
{
return x_571;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_571, 0);
x_581 = lean_ctor_get(x_571, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_571);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_564);
if (x_583 == 0)
{
return x_564;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_564, 0);
x_585 = lean_ctor_get(x_564, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_564);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_600; lean_object* x_601; uint8_t x_602; 
lean_dec(x_5);
lean_dec(x_1);
x_587 = lean_ctor_get(x_2, 0);
lean_inc(x_587);
x_588 = lean_array_get_size(x_587);
lean_dec(x_587);
x_589 = lean_ctor_get(x_2, 2);
lean_inc(x_589);
x_600 = lean_nat_add(x_588, x_589);
x_601 = lean_array_get_size(x_6);
x_602 = lean_nat_dec_le(x_601, x_600);
lean_dec(x_601);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_603 = l_Lean_Expr_Inhabited;
x_604 = lean_array_get(x_603, x_6, x_600);
lean_dec(x_600);
x_605 = lean_ctor_get(x_2, 6);
lean_inc(x_605);
x_606 = lean_array_get_size(x_605);
lean_dec(x_605);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_607 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_606, x_604, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_590 = x_608;
x_591 = x_609;
goto block_599;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_6);
lean_dec(x_2);
x_610 = lean_ctor_get(x_607, 1);
lean_inc(x_610);
lean_dec(x_607);
x_611 = l_Lean_indentExpr(x_4);
x_612 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_613 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
x_614 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_615 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
x_616 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_615, x_8, x_9, x_10, x_11, x_610);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_617 = !lean_is_exclusive(x_616);
if (x_617 == 0)
{
return x_616;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_616, 0);
x_619 = lean_ctor_get(x_616, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_616);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
lean_dec(x_600);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_621 = l_Lean_indentExpr(x_4);
x_622 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_623 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_621);
x_624 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_625 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
x_626 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_625, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
return x_626;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_626);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
block_599:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_592 = lean_array_get_size(x_6);
lean_inc(x_6);
x_593 = l_Array_extract___rarg(x_6, x_588, x_592);
x_594 = lean_unsigned_to_nat(0u);
x_595 = l_Array_empty___closed__1;
x_596 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_589, x_593, x_593, x_594, x_595);
lean_dec(x_593);
lean_dec(x_589);
lean_dec(x_6);
lean_dec(x_2);
x_597 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_596, x_596, x_594, x_590);
lean_dec(x_596);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_591);
return x_598;
}
}
}
case 10:
{
uint8_t x_631; 
lean_dec(x_7);
x_631 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_632 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = x_6;
x_636 = lean_unsigned_to_nat(0u);
x_637 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_637, 0, x_1);
lean_closure_set(x_637, 1, x_2);
lean_closure_set(x_637, 2, x_3);
lean_closure_set(x_637, 3, x_636);
lean_closure_set(x_637, 4, x_635);
x_638 = x_637;
x_639 = lean_apply_5(x_638, x_8, x_9, x_10, x_11, x_634);
if (lean_obj_tag(x_639) == 0)
{
uint8_t x_640; 
x_640 = !lean_is_exclusive(x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; 
x_641 = lean_ctor_get(x_639, 0);
x_642 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_641, x_641, x_636, x_633);
lean_dec(x_641);
lean_ctor_set(x_639, 0, x_642);
return x_639;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_643 = lean_ctor_get(x_639, 0);
x_644 = lean_ctor_get(x_639, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_639);
x_645 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_643, x_643, x_636, x_633);
lean_dec(x_643);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
uint8_t x_647; 
lean_dec(x_633);
x_647 = !lean_is_exclusive(x_639);
if (x_647 == 0)
{
return x_639;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_639, 0);
x_649 = lean_ctor_get(x_639, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_639);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
else
{
uint8_t x_651; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_651 = !lean_is_exclusive(x_632);
if (x_651 == 0)
{
return x_632;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_632, 0);
x_653 = lean_ctor_get(x_632, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_632);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
lean_dec(x_5);
lean_dec(x_1);
x_655 = lean_ctor_get(x_2, 0);
lean_inc(x_655);
x_656 = lean_array_get_size(x_655);
lean_dec(x_655);
x_657 = lean_ctor_get(x_2, 2);
lean_inc(x_657);
x_668 = lean_nat_add(x_656, x_657);
x_669 = lean_array_get_size(x_6);
x_670 = lean_nat_dec_le(x_669, x_668);
lean_dec(x_669);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_671 = l_Lean_Expr_Inhabited;
x_672 = lean_array_get(x_671, x_6, x_668);
lean_dec(x_668);
x_673 = lean_ctor_get(x_2, 6);
lean_inc(x_673);
x_674 = lean_array_get_size(x_673);
lean_dec(x_673);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_675 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_674, x_672, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_658 = x_676;
x_659 = x_677;
goto block_667;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_2);
x_678 = lean_ctor_get(x_675, 1);
lean_inc(x_678);
lean_dec(x_675);
x_679 = l_Lean_indentExpr(x_4);
x_680 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_681 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_679);
x_682 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_683 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
x_684 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_683, x_8, x_9, x_10, x_11, x_678);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_685 = !lean_is_exclusive(x_684);
if (x_685 == 0)
{
return x_684;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_684, 0);
x_687 = lean_ctor_get(x_684, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_684);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
return x_688;
}
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
lean_dec(x_668);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_689 = l_Lean_indentExpr(x_4);
x_690 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_691 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_692 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_693 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
x_694 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_693, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_695 = !lean_is_exclusive(x_694);
if (x_695 == 0)
{
return x_694;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_694, 0);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_inc(x_696);
lean_dec(x_694);
x_698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
return x_698;
}
}
block_667:
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_660 = lean_array_get_size(x_6);
lean_inc(x_6);
x_661 = l_Array_extract___rarg(x_6, x_656, x_660);
x_662 = lean_unsigned_to_nat(0u);
x_663 = l_Array_empty___closed__1;
x_664 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_657, x_661, x_661, x_662, x_663);
lean_dec(x_661);
lean_dec(x_657);
lean_dec(x_6);
lean_dec(x_2);
x_665 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_664, x_664, x_662, x_658);
lean_dec(x_664);
x_666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_659);
return x_666;
}
}
}
case 11:
{
uint8_t x_699; 
lean_dec(x_7);
x_699 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_699 == 0)
{
lean_object* x_700; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_700 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = x_6;
x_704 = lean_unsigned_to_nat(0u);
x_705 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_705, 0, x_1);
lean_closure_set(x_705, 1, x_2);
lean_closure_set(x_705, 2, x_3);
lean_closure_set(x_705, 3, x_704);
lean_closure_set(x_705, 4, x_703);
x_706 = x_705;
x_707 = lean_apply_5(x_706, x_8, x_9, x_10, x_11, x_702);
if (lean_obj_tag(x_707) == 0)
{
uint8_t x_708; 
x_708 = !lean_is_exclusive(x_707);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_707, 0);
x_710 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_709, x_709, x_704, x_701);
lean_dec(x_709);
lean_ctor_set(x_707, 0, x_710);
return x_707;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_711 = lean_ctor_get(x_707, 0);
x_712 = lean_ctor_get(x_707, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_707);
x_713 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_711, x_711, x_704, x_701);
lean_dec(x_711);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_712);
return x_714;
}
}
else
{
uint8_t x_715; 
lean_dec(x_701);
x_715 = !lean_is_exclusive(x_707);
if (x_715 == 0)
{
return x_707;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_707, 0);
x_717 = lean_ctor_get(x_707, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_707);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
}
else
{
uint8_t x_719; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_719 = !lean_is_exclusive(x_700);
if (x_719 == 0)
{
return x_700;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_720 = lean_ctor_get(x_700, 0);
x_721 = lean_ctor_get(x_700, 1);
lean_inc(x_721);
lean_inc(x_720);
lean_dec(x_700);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
return x_722;
}
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_736; lean_object* x_737; uint8_t x_738; 
lean_dec(x_5);
lean_dec(x_1);
x_723 = lean_ctor_get(x_2, 0);
lean_inc(x_723);
x_724 = lean_array_get_size(x_723);
lean_dec(x_723);
x_725 = lean_ctor_get(x_2, 2);
lean_inc(x_725);
x_736 = lean_nat_add(x_724, x_725);
x_737 = lean_array_get_size(x_6);
x_738 = lean_nat_dec_le(x_737, x_736);
lean_dec(x_737);
if (x_738 == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_739 = l_Lean_Expr_Inhabited;
x_740 = lean_array_get(x_739, x_6, x_736);
lean_dec(x_736);
x_741 = lean_ctor_get(x_2, 6);
lean_inc(x_741);
x_742 = lean_array_get_size(x_741);
lean_dec(x_741);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_743 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_742, x_740, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_726 = x_744;
x_727 = x_745;
goto block_735;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
lean_dec(x_725);
lean_dec(x_724);
lean_dec(x_6);
lean_dec(x_2);
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
lean_dec(x_743);
x_747 = l_Lean_indentExpr(x_4);
x_748 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_749 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_747);
x_750 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_751 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
x_752 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_751, x_8, x_9, x_10, x_11, x_746);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_753 = !lean_is_exclusive(x_752);
if (x_753 == 0)
{
return x_752;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_752, 0);
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_752);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; 
lean_dec(x_736);
lean_dec(x_725);
lean_dec(x_724);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_757 = l_Lean_indentExpr(x_4);
x_758 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_759 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
x_760 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_761 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
x_762 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_761, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_763 = !lean_is_exclusive(x_762);
if (x_763 == 0)
{
return x_762;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_762, 0);
x_765 = lean_ctor_get(x_762, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_762);
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
return x_766;
}
}
block_735:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_728 = lean_array_get_size(x_6);
lean_inc(x_6);
x_729 = l_Array_extract___rarg(x_6, x_724, x_728);
x_730 = lean_unsigned_to_nat(0u);
x_731 = l_Array_empty___closed__1;
x_732 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_725, x_729, x_729, x_730, x_731);
lean_dec(x_729);
lean_dec(x_725);
lean_dec(x_6);
lean_dec(x_2);
x_733 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_732, x_732, x_730, x_726);
lean_dec(x_732);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_727);
return x_734;
}
}
}
default: 
{
uint8_t x_767; 
lean_dec(x_7);
x_767 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_767 == 0)
{
lean_object* x_768; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_768 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
x_771 = x_6;
x_772 = lean_unsigned_to_nat(0u);
x_773 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_773, 0, x_1);
lean_closure_set(x_773, 1, x_2);
lean_closure_set(x_773, 2, x_3);
lean_closure_set(x_773, 3, x_772);
lean_closure_set(x_773, 4, x_771);
x_774 = x_773;
x_775 = lean_apply_5(x_774, x_8, x_9, x_10, x_11, x_770);
if (lean_obj_tag(x_775) == 0)
{
uint8_t x_776; 
x_776 = !lean_is_exclusive(x_775);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; 
x_777 = lean_ctor_get(x_775, 0);
x_778 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_777, x_777, x_772, x_769);
lean_dec(x_777);
lean_ctor_set(x_775, 0, x_778);
return x_775;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_779 = lean_ctor_get(x_775, 0);
x_780 = lean_ctor_get(x_775, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_775);
x_781 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_779, x_779, x_772, x_769);
lean_dec(x_779);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
else
{
uint8_t x_783; 
lean_dec(x_769);
x_783 = !lean_is_exclusive(x_775);
if (x_783 == 0)
{
return x_775;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_775, 0);
x_785 = lean_ctor_get(x_775, 1);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_775);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
return x_786;
}
}
}
else
{
uint8_t x_787; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_787 = !lean_is_exclusive(x_768);
if (x_787 == 0)
{
return x_768;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_768, 0);
x_789 = lean_ctor_get(x_768, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_768);
x_790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_790, 0, x_788);
lean_ctor_set(x_790, 1, x_789);
return x_790;
}
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_804; lean_object* x_805; uint8_t x_806; 
lean_dec(x_5);
lean_dec(x_1);
x_791 = lean_ctor_get(x_2, 0);
lean_inc(x_791);
x_792 = lean_array_get_size(x_791);
lean_dec(x_791);
x_793 = lean_ctor_get(x_2, 2);
lean_inc(x_793);
x_804 = lean_nat_add(x_792, x_793);
x_805 = lean_array_get_size(x_6);
x_806 = lean_nat_dec_le(x_805, x_804);
lean_dec(x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_807 = l_Lean_Expr_Inhabited;
x_808 = lean_array_get(x_807, x_6, x_804);
lean_dec(x_804);
x_809 = lean_ctor_get(x_2, 6);
lean_inc(x_809);
x_810 = lean_array_get_size(x_809);
lean_dec(x_809);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_811 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_810, x_808, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_794 = x_812;
x_795 = x_813;
goto block_803;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; uint8_t x_821; 
lean_dec(x_793);
lean_dec(x_792);
lean_dec(x_6);
lean_dec(x_2);
x_814 = lean_ctor_get(x_811, 1);
lean_inc(x_814);
lean_dec(x_811);
x_815 = l_Lean_indentExpr(x_4);
x_816 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_817 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_815);
x_818 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_819 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
x_820 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_819, x_8, x_9, x_10, x_11, x_814);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_821 = !lean_is_exclusive(x_820);
if (x_821 == 0)
{
return x_820;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_820, 0);
x_823 = lean_ctor_get(x_820, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_820);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; 
lean_dec(x_804);
lean_dec(x_793);
lean_dec(x_792);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_825 = l_Lean_indentExpr(x_4);
x_826 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_827 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_825);
x_828 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_829 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_829, 0, x_827);
lean_ctor_set(x_829, 1, x_828);
x_830 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_829, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_831 = !lean_is_exclusive(x_830);
if (x_831 == 0)
{
return x_830;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_832 = lean_ctor_get(x_830, 0);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_inc(x_832);
lean_dec(x_830);
x_834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_834, 0, x_832);
lean_ctor_set(x_834, 1, x_833);
return x_834;
}
}
block_803:
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_796 = lean_array_get_size(x_6);
lean_inc(x_6);
x_797 = l_Array_extract___rarg(x_6, x_792, x_796);
x_798 = lean_unsigned_to_nat(0u);
x_799 = l_Array_empty___closed__1;
x_800 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_2, x_6, x_793, x_797, x_797, x_798, x_799);
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_6);
lean_dec(x_2);
x_801 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_800, x_800, x_798, x_794);
lean_dec(x_800);
x_802 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_795);
return x_802;
}
}
}
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_Basic_23__lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected matcher application alternative");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nat application");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("altNumParams: ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", xs: ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_43; lean_object* x_44; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_st_ref_get(x_11, x_12);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = 0;
x_43 = x_66;
x_44 = x_65;
goto block_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_69 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_68, x_8, x_9, x_10, x_11, x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_43 = x_72;
x_44 = x_71;
goto block_60;
}
block_42:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_le(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = l_Lean_indentExpr(x_2);
x_17 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_3);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_24, x_8, x_9, x_10, x_11, x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_1, x_30);
lean_dec(x_1);
x_32 = l_Lean_Expr_Inhabited;
x_33 = lean_array_get(x_32, x_6, x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_4, x_5, x_33, x_7, x_8, x_9, x_10, x_11, x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__2(x_6, x_35, x_8, x_9, x_10, x_11, x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
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
}
block_60:
{
if (x_43 == 0)
{
x_13 = x_44;
goto block_42;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_inc(x_1);
x_45 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_1);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__6;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__8;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Array_toList___rarg(x_6);
x_52 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_51);
x_53 = l_Lean_MessageData_ofList(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_58 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_57, x_56, x_8, x_9, x_10, x_11, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_13 = x_59;
goto block_42;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_5;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_fget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_5, x_4, x_16);
x_18 = x_15;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1), 12, 5);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7___rarg(x_19, x_21, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
x_27 = x_23;
x_28 = lean_array_fset(x_17, x_4, x_27);
lean_dec(x_4);
x_4 = x_26;
x_5 = x_28;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_5;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_5, x_4, x_16);
x_18 = x_15;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
x_24 = x_20;
x_25 = lean_array_fset(x_17, x_4, x_24);
lean_dec(x_4);
x_4 = x_23;
x_5 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_5, x_6);
x_11 = lean_nat_dec_eq(x_3, x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
if (x_11 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 3);
x_15 = l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_14, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_push(x_7, x_10);
x_6 = x_13;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_10);
x_6 = x_13;
goto _start;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
x_6 = x_13;
goto _start;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = x_6;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_17);
x_20 = x_19;
x_21 = lean_apply_5(x_20, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_23, x_23, x_18, x_15);
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
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_25, x_25, x_18, x_15);
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
lean_dec(x_15);
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
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_array_get_size(x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_50 = lean_nat_add(x_38, x_39);
x_51 = lean_array_get_size(x_6);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_Expr_Inhabited;
x_54 = lean_array_get(x_53, x_6, x_50);
lean_dec(x_50);
x_55 = lean_ctor_get(x_2, 6);
lean_inc(x_55);
x_56 = lean_array_get_size(x_55);
lean_dec(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_56, x_54, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_40 = x_58;
x_41 = x_59;
goto block_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_2);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_indentExpr(x_4);
x_62 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_65, x_8, x_9, x_10, x_11, x_60);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_71 = l_Lean_indentExpr(x_4);
x_72 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_75, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
block_49:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_array_get_size(x_6);
lean_inc(x_6);
x_43 = l_Array_extract___rarg(x_6, x_38, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_empty___closed__1;
x_46 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_39, x_43, x_43, x_44, x_45);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_2);
x_47 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_46, x_46, x_44, x_40);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
}
}
case 1:
{
uint8_t x_81; 
lean_dec(x_7);
x_81 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = x_6;
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_87, 0, x_1);
lean_closure_set(x_87, 1, x_2);
lean_closure_set(x_87, 2, x_3);
lean_closure_set(x_87, 3, x_86);
lean_closure_set(x_87, 4, x_85);
x_88 = x_87;
x_89 = lean_apply_5(x_88, x_8, x_9, x_10, x_11, x_84);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_91, x_91, x_86, x_83);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_93, x_93, x_86, x_83);
lean_dec(x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_83);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
return x_82;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_82, 0);
x_103 = lean_ctor_get(x_82, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_82);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_5);
lean_dec(x_1);
x_105 = lean_ctor_get(x_2, 0);
lean_inc(x_105);
x_106 = lean_array_get_size(x_105);
lean_dec(x_105);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
x_118 = lean_nat_add(x_106, x_107);
x_119 = lean_array_get_size(x_6);
x_120 = lean_nat_dec_le(x_119, x_118);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Lean_Expr_Inhabited;
x_122 = lean_array_get(x_121, x_6, x_118);
lean_dec(x_118);
x_123 = lean_ctor_get(x_2, 6);
lean_inc(x_123);
x_124 = lean_array_get_size(x_123);
lean_dec(x_123);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_125 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_124, x_122, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_108 = x_126;
x_109 = x_127;
goto block_117;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_2);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l_Lean_indentExpr(x_4);
x_130 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_133, x_8, x_9, x_10, x_11, x_128);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
return x_134;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_134);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_118);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_139 = l_Lean_indentExpr(x_4);
x_140 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_143, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
block_117:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_array_get_size(x_6);
lean_inc(x_6);
x_111 = l_Array_extract___rarg(x_6, x_106, x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Array_empty___closed__1;
x_114 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_107, x_111, x_111, x_112, x_113);
lean_dec(x_111);
lean_dec(x_107);
lean_dec(x_6);
lean_dec(x_2);
x_115 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_114, x_114, x_112, x_108);
lean_dec(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
return x_116;
}
}
}
case 2:
{
uint8_t x_149; 
lean_dec(x_7);
x_149 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_150 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = x_6;
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_155, 0, x_1);
lean_closure_set(x_155, 1, x_2);
lean_closure_set(x_155, 2, x_3);
lean_closure_set(x_155, 3, x_154);
lean_closure_set(x_155, 4, x_153);
x_156 = x_155;
x_157 = lean_apply_5(x_156, x_8, x_9, x_10, x_11, x_152);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_159, x_159, x_154, x_151);
lean_dec(x_159);
lean_ctor_set(x_157, 0, x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_157, 0);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_157);
x_163 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_161, x_161, x_154, x_151);
lean_dec(x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_151);
x_165 = !lean_is_exclusive(x_157);
if (x_165 == 0)
{
return x_157;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_157, 0);
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_157);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_150);
if (x_169 == 0)
{
return x_150;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_150, 0);
x_171 = lean_ctor_get(x_150, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_150);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_5);
lean_dec(x_1);
x_173 = lean_ctor_get(x_2, 0);
lean_inc(x_173);
x_174 = lean_array_get_size(x_173);
lean_dec(x_173);
x_175 = lean_ctor_get(x_2, 2);
lean_inc(x_175);
x_186 = lean_nat_add(x_174, x_175);
x_187 = lean_array_get_size(x_6);
x_188 = lean_nat_dec_le(x_187, x_186);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = l_Lean_Expr_Inhabited;
x_190 = lean_array_get(x_189, x_6, x_186);
lean_dec(x_186);
x_191 = lean_ctor_get(x_2, 6);
lean_inc(x_191);
x_192 = lean_array_get_size(x_191);
lean_dec(x_191);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_193 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_192, x_190, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_176 = x_194;
x_177 = x_195;
goto block_185;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec(x_2);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = l_Lean_indentExpr(x_4);
x_198 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_201, x_8, x_9, x_10, x_11, x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
return x_202;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_202);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_186);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_207 = l_Lean_indentExpr(x_4);
x_208 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_211, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
return x_212;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_212);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
block_185:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_array_get_size(x_6);
lean_inc(x_6);
x_179 = l_Array_extract___rarg(x_6, x_174, x_178);
x_180 = lean_unsigned_to_nat(0u);
x_181 = l_Array_empty___closed__1;
x_182 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_175, x_179, x_179, x_180, x_181);
lean_dec(x_179);
lean_dec(x_175);
lean_dec(x_6);
lean_dec(x_2);
x_183 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_182, x_182, x_180, x_176);
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_177);
return x_184;
}
}
}
case 3:
{
uint8_t x_217; 
lean_dec(x_7);
x_217 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_218 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = x_6;
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_223, 0, x_1);
lean_closure_set(x_223, 1, x_2);
lean_closure_set(x_223, 2, x_3);
lean_closure_set(x_223, 3, x_222);
lean_closure_set(x_223, 4, x_221);
x_224 = x_223;
x_225 = lean_apply_5(x_224, x_8, x_9, x_10, x_11, x_220);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_227, x_227, x_222, x_219);
lean_dec(x_227);
lean_ctor_set(x_225, 0, x_228);
return x_225;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_225, 0);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_225);
x_231 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_229, x_229, x_222, x_219);
lean_dec(x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_219);
x_233 = !lean_is_exclusive(x_225);
if (x_233 == 0)
{
return x_225;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_225, 0);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_225);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_218);
if (x_237 == 0)
{
return x_218;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_218, 0);
x_239 = lean_ctor_get(x_218, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_218);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_dec(x_5);
lean_dec(x_1);
x_241 = lean_ctor_get(x_2, 0);
lean_inc(x_241);
x_242 = lean_array_get_size(x_241);
lean_dec(x_241);
x_243 = lean_ctor_get(x_2, 2);
lean_inc(x_243);
x_254 = lean_nat_add(x_242, x_243);
x_255 = lean_array_get_size(x_6);
x_256 = lean_nat_dec_le(x_255, x_254);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_257 = l_Lean_Expr_Inhabited;
x_258 = lean_array_get(x_257, x_6, x_254);
lean_dec(x_254);
x_259 = lean_ctor_get(x_2, 6);
lean_inc(x_259);
x_260 = lean_array_get_size(x_259);
lean_dec(x_259);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_261 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_260, x_258, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_244 = x_262;
x_245 = x_263;
goto block_253;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_6);
lean_dec(x_2);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = l_Lean_indentExpr(x_4);
x_266 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_267 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_269 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_269, x_8, x_9, x_10, x_11, x_264);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
return x_270;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_270, 0);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_270);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_275 = l_Lean_indentExpr(x_4);
x_276 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_277 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_279 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_279, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
return x_280;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_280);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
block_253:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_array_get_size(x_6);
lean_inc(x_6);
x_247 = l_Array_extract___rarg(x_6, x_242, x_246);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l_Array_empty___closed__1;
x_250 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_243, x_247, x_247, x_248, x_249);
lean_dec(x_247);
lean_dec(x_243);
lean_dec(x_6);
lean_dec(x_2);
x_251 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_250, x_250, x_248, x_244);
lean_dec(x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_245);
return x_252;
}
}
}
case 4:
{
uint8_t x_285; 
lean_dec(x_7);
x_285 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_285 == 0)
{
lean_object* x_286; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_286 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = x_6;
x_290 = lean_unsigned_to_nat(0u);
x_291 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_291, 0, x_1);
lean_closure_set(x_291, 1, x_2);
lean_closure_set(x_291, 2, x_3);
lean_closure_set(x_291, 3, x_290);
lean_closure_set(x_291, 4, x_289);
x_292 = x_291;
x_293 = lean_apply_5(x_292, x_8, x_9, x_10, x_11, x_288);
if (lean_obj_tag(x_293) == 0)
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_293, 0);
x_296 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_295, x_295, x_290, x_287);
lean_dec(x_295);
lean_ctor_set(x_293, 0, x_296);
return x_293;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_293, 0);
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_293);
x_299 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_297, x_297, x_290, x_287);
lean_dec(x_297);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
uint8_t x_301; 
lean_dec(x_287);
x_301 = !lean_is_exclusive(x_293);
if (x_301 == 0)
{
return x_293;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_293, 0);
x_303 = lean_ctor_get(x_293, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_293);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_286);
if (x_305 == 0)
{
return x_286;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_286, 0);
x_307 = lean_ctor_get(x_286, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_286);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_5);
lean_dec(x_1);
x_309 = lean_ctor_get(x_2, 0);
lean_inc(x_309);
x_310 = lean_array_get_size(x_309);
lean_dec(x_309);
x_311 = lean_ctor_get(x_2, 2);
lean_inc(x_311);
x_322 = lean_nat_add(x_310, x_311);
x_323 = lean_array_get_size(x_6);
x_324 = lean_nat_dec_le(x_323, x_322);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = l_Lean_Expr_Inhabited;
x_326 = lean_array_get(x_325, x_6, x_322);
lean_dec(x_322);
x_327 = lean_ctor_get(x_2, 6);
lean_inc(x_327);
x_328 = lean_array_get_size(x_327);
lean_dec(x_327);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_329 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_328, x_326, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_312 = x_330;
x_313 = x_331;
goto block_321;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_6);
lean_dec(x_2);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = l_Lean_indentExpr(x_4);
x_334 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_335 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_337 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_337, x_8, x_9, x_10, x_11, x_332);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
return x_338;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_338, 0);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_338);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
lean_dec(x_322);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_343 = l_Lean_indentExpr(x_4);
x_344 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_345 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_343);
x_346 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_347 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_347, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
return x_348;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_348, 0);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_348);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
block_321:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_314 = lean_array_get_size(x_6);
lean_inc(x_6);
x_315 = l_Array_extract___rarg(x_6, x_310, x_314);
x_316 = lean_unsigned_to_nat(0u);
x_317 = l_Array_empty___closed__1;
x_318 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_311, x_315, x_315, x_316, x_317);
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_6);
lean_dec(x_2);
x_319 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_318, x_318, x_316, x_312);
lean_dec(x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_313);
return x_320;
}
}
}
case 5:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_5, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_5, 1);
lean_inc(x_354);
lean_dec(x_5);
x_355 = lean_array_set(x_6, x_7, x_354);
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_sub(x_7, x_356);
lean_dec(x_7);
x_5 = x_353;
x_6 = x_355;
x_7 = x_357;
goto _start;
}
case 6:
{
uint8_t x_359; 
lean_dec(x_7);
x_359 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_359 == 0)
{
lean_object* x_360; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_360 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = x_6;
x_364 = lean_unsigned_to_nat(0u);
x_365 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_365, 0, x_1);
lean_closure_set(x_365, 1, x_2);
lean_closure_set(x_365, 2, x_3);
lean_closure_set(x_365, 3, x_364);
lean_closure_set(x_365, 4, x_363);
x_366 = x_365;
x_367 = lean_apply_5(x_366, x_8, x_9, x_10, x_11, x_362);
if (lean_obj_tag(x_367) == 0)
{
uint8_t x_368; 
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_369, x_369, x_364, x_361);
lean_dec(x_369);
lean_ctor_set(x_367, 0, x_370);
return x_367;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_367, 0);
x_372 = lean_ctor_get(x_367, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_367);
x_373 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_371, x_371, x_364, x_361);
lean_dec(x_371);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
else
{
uint8_t x_375; 
lean_dec(x_361);
x_375 = !lean_is_exclusive(x_367);
if (x_375 == 0)
{
return x_367;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_367, 0);
x_377 = lean_ctor_get(x_367, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_367);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_379 = !lean_is_exclusive(x_360);
if (x_379 == 0)
{
return x_360;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_360, 0);
x_381 = lean_ctor_get(x_360, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_360);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_5);
lean_dec(x_1);
x_383 = lean_ctor_get(x_2, 0);
lean_inc(x_383);
x_384 = lean_array_get_size(x_383);
lean_dec(x_383);
x_385 = lean_ctor_get(x_2, 2);
lean_inc(x_385);
x_396 = lean_nat_add(x_384, x_385);
x_397 = lean_array_get_size(x_6);
x_398 = lean_nat_dec_le(x_397, x_396);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = l_Lean_Expr_Inhabited;
x_400 = lean_array_get(x_399, x_6, x_396);
lean_dec(x_396);
x_401 = lean_ctor_get(x_2, 6);
lean_inc(x_401);
x_402 = lean_array_get_size(x_401);
lean_dec(x_401);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_403 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_402, x_400, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_386 = x_404;
x_387 = x_405;
goto block_395;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_6);
lean_dec(x_2);
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
lean_dec(x_403);
x_407 = l_Lean_indentExpr(x_4);
x_408 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_409 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
x_410 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_411 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_411, x_8, x_9, x_10, x_11, x_406);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_413 = !lean_is_exclusive(x_412);
if (x_413 == 0)
{
return x_412;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_412, 0);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_412);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
lean_dec(x_396);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_417 = l_Lean_indentExpr(x_4);
x_418 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_419 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_417);
x_420 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_421 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_421, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
return x_422;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_422, 0);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_422);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
block_395:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = lean_array_get_size(x_6);
lean_inc(x_6);
x_389 = l_Array_extract___rarg(x_6, x_384, x_388);
x_390 = lean_unsigned_to_nat(0u);
x_391 = l_Array_empty___closed__1;
x_392 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_385, x_389, x_389, x_390, x_391);
lean_dec(x_389);
lean_dec(x_385);
lean_dec(x_6);
lean_dec(x_2);
x_393 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_392, x_392, x_390, x_386);
lean_dec(x_392);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_387);
return x_394;
}
}
}
case 7:
{
uint8_t x_427; 
lean_dec(x_7);
x_427 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_428 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = x_6;
x_432 = lean_unsigned_to_nat(0u);
x_433 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_433, 0, x_1);
lean_closure_set(x_433, 1, x_2);
lean_closure_set(x_433, 2, x_3);
lean_closure_set(x_433, 3, x_432);
lean_closure_set(x_433, 4, x_431);
x_434 = x_433;
x_435 = lean_apply_5(x_434, x_8, x_9, x_10, x_11, x_430);
if (lean_obj_tag(x_435) == 0)
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_435);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
x_437 = lean_ctor_get(x_435, 0);
x_438 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_437, x_437, x_432, x_429);
lean_dec(x_437);
lean_ctor_set(x_435, 0, x_438);
return x_435;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_439 = lean_ctor_get(x_435, 0);
x_440 = lean_ctor_get(x_435, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_435);
x_441 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_439, x_439, x_432, x_429);
lean_dec(x_439);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
uint8_t x_443; 
lean_dec(x_429);
x_443 = !lean_is_exclusive(x_435);
if (x_443 == 0)
{
return x_435;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_435, 0);
x_445 = lean_ctor_get(x_435, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_435);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_447 = !lean_is_exclusive(x_428);
if (x_447 == 0)
{
return x_428;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_428, 0);
x_449 = lean_ctor_get(x_428, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_428);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
lean_dec(x_5);
lean_dec(x_1);
x_451 = lean_ctor_get(x_2, 0);
lean_inc(x_451);
x_452 = lean_array_get_size(x_451);
lean_dec(x_451);
x_453 = lean_ctor_get(x_2, 2);
lean_inc(x_453);
x_464 = lean_nat_add(x_452, x_453);
x_465 = lean_array_get_size(x_6);
x_466 = lean_nat_dec_le(x_465, x_464);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_467 = l_Lean_Expr_Inhabited;
x_468 = lean_array_get(x_467, x_6, x_464);
lean_dec(x_464);
x_469 = lean_ctor_get(x_2, 6);
lean_inc(x_469);
x_470 = lean_array_get_size(x_469);
lean_dec(x_469);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_471 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_470, x_468, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_454 = x_472;
x_455 = x_473;
goto block_463;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; 
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_6);
lean_dec(x_2);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
lean_dec(x_471);
x_475 = l_Lean_indentExpr(x_4);
x_476 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_477 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_475);
x_478 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_479 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_479, x_8, x_9, x_10, x_11, x_474);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_481 = !lean_is_exclusive(x_480);
if (x_481 == 0)
{
return x_480;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_480, 0);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_480);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
lean_dec(x_464);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_485 = l_Lean_indentExpr(x_4);
x_486 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_487 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_489, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_491 = !lean_is_exclusive(x_490);
if (x_491 == 0)
{
return x_490;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_490, 0);
x_493 = lean_ctor_get(x_490, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_490);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
block_463:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_456 = lean_array_get_size(x_6);
lean_inc(x_6);
x_457 = l_Array_extract___rarg(x_6, x_452, x_456);
x_458 = lean_unsigned_to_nat(0u);
x_459 = l_Array_empty___closed__1;
x_460 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_453, x_457, x_457, x_458, x_459);
lean_dec(x_457);
lean_dec(x_453);
lean_dec(x_6);
lean_dec(x_2);
x_461 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_460, x_460, x_458, x_454);
lean_dec(x_460);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_455);
return x_462;
}
}
}
case 8:
{
uint8_t x_495; 
lean_dec(x_7);
x_495 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_496 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_499 = x_6;
x_500 = lean_unsigned_to_nat(0u);
x_501 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_501, 0, x_1);
lean_closure_set(x_501, 1, x_2);
lean_closure_set(x_501, 2, x_3);
lean_closure_set(x_501, 3, x_500);
lean_closure_set(x_501, 4, x_499);
x_502 = x_501;
x_503 = lean_apply_5(x_502, x_8, x_9, x_10, x_11, x_498);
if (lean_obj_tag(x_503) == 0)
{
uint8_t x_504; 
x_504 = !lean_is_exclusive(x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_503, 0);
x_506 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_505, x_505, x_500, x_497);
lean_dec(x_505);
lean_ctor_set(x_503, 0, x_506);
return x_503;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_503, 0);
x_508 = lean_ctor_get(x_503, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_503);
x_509 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_507, x_507, x_500, x_497);
lean_dec(x_507);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
uint8_t x_511; 
lean_dec(x_497);
x_511 = !lean_is_exclusive(x_503);
if (x_511 == 0)
{
return x_503;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_503, 0);
x_513 = lean_ctor_get(x_503, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_503);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
return x_514;
}
}
}
else
{
uint8_t x_515; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_515 = !lean_is_exclusive(x_496);
if (x_515 == 0)
{
return x_496;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_496, 0);
x_517 = lean_ctor_get(x_496, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_496);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
return x_518;
}
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
lean_dec(x_5);
lean_dec(x_1);
x_519 = lean_ctor_get(x_2, 0);
lean_inc(x_519);
x_520 = lean_array_get_size(x_519);
lean_dec(x_519);
x_521 = lean_ctor_get(x_2, 2);
lean_inc(x_521);
x_532 = lean_nat_add(x_520, x_521);
x_533 = lean_array_get_size(x_6);
x_534 = lean_nat_dec_le(x_533, x_532);
lean_dec(x_533);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_535 = l_Lean_Expr_Inhabited;
x_536 = lean_array_get(x_535, x_6, x_532);
lean_dec(x_532);
x_537 = lean_ctor_get(x_2, 6);
lean_inc(x_537);
x_538 = lean_array_get_size(x_537);
lean_dec(x_537);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_539 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_538, x_536, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_522 = x_540;
x_523 = x_541;
goto block_531;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_2);
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_543 = l_Lean_indentExpr(x_4);
x_544 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_545 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_547 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
x_548 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_547, x_8, x_9, x_10, x_11, x_542);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
return x_548;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_548, 0);
x_551 = lean_ctor_get(x_548, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_548);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
lean_dec(x_532);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_553 = l_Lean_indentExpr(x_4);
x_554 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_555 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_553);
x_556 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_557 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
x_558 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_557, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_559 = !lean_is_exclusive(x_558);
if (x_559 == 0)
{
return x_558;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_558, 0);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_558);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
block_531:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_524 = lean_array_get_size(x_6);
lean_inc(x_6);
x_525 = l_Array_extract___rarg(x_6, x_520, x_524);
x_526 = lean_unsigned_to_nat(0u);
x_527 = l_Array_empty___closed__1;
x_528 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_521, x_525, x_525, x_526, x_527);
lean_dec(x_525);
lean_dec(x_521);
lean_dec(x_6);
lean_dec(x_2);
x_529 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_528, x_528, x_526, x_522);
lean_dec(x_528);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_523);
return x_530;
}
}
}
case 9:
{
uint8_t x_563; 
lean_dec(x_7);
x_563 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_564 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = x_6;
x_568 = lean_unsigned_to_nat(0u);
x_569 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_569, 0, x_1);
lean_closure_set(x_569, 1, x_2);
lean_closure_set(x_569, 2, x_3);
lean_closure_set(x_569, 3, x_568);
lean_closure_set(x_569, 4, x_567);
x_570 = x_569;
x_571 = lean_apply_5(x_570, x_8, x_9, x_10, x_11, x_566);
if (lean_obj_tag(x_571) == 0)
{
uint8_t x_572; 
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_571, 0);
x_574 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_573, x_573, x_568, x_565);
lean_dec(x_573);
lean_ctor_set(x_571, 0, x_574);
return x_571;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_575 = lean_ctor_get(x_571, 0);
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_571);
x_577 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_575, x_575, x_568, x_565);
lean_dec(x_575);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
else
{
uint8_t x_579; 
lean_dec(x_565);
x_579 = !lean_is_exclusive(x_571);
if (x_579 == 0)
{
return x_571;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_571, 0);
x_581 = lean_ctor_get(x_571, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_571);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_564);
if (x_583 == 0)
{
return x_564;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_564, 0);
x_585 = lean_ctor_get(x_564, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_564);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_600; lean_object* x_601; uint8_t x_602; 
lean_dec(x_5);
lean_dec(x_1);
x_587 = lean_ctor_get(x_2, 0);
lean_inc(x_587);
x_588 = lean_array_get_size(x_587);
lean_dec(x_587);
x_589 = lean_ctor_get(x_2, 2);
lean_inc(x_589);
x_600 = lean_nat_add(x_588, x_589);
x_601 = lean_array_get_size(x_6);
x_602 = lean_nat_dec_le(x_601, x_600);
lean_dec(x_601);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_603 = l_Lean_Expr_Inhabited;
x_604 = lean_array_get(x_603, x_6, x_600);
lean_dec(x_600);
x_605 = lean_ctor_get(x_2, 6);
lean_inc(x_605);
x_606 = lean_array_get_size(x_605);
lean_dec(x_605);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_607 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_606, x_604, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_590 = x_608;
x_591 = x_609;
goto block_599;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_6);
lean_dec(x_2);
x_610 = lean_ctor_get(x_607, 1);
lean_inc(x_610);
lean_dec(x_607);
x_611 = l_Lean_indentExpr(x_4);
x_612 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_613 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
x_614 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_615 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
x_616 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_615, x_8, x_9, x_10, x_11, x_610);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_617 = !lean_is_exclusive(x_616);
if (x_617 == 0)
{
return x_616;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_616, 0);
x_619 = lean_ctor_get(x_616, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_616);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
lean_dec(x_600);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_621 = l_Lean_indentExpr(x_4);
x_622 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_623 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_621);
x_624 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_625 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
x_626 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_625, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
return x_626;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_626);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
block_599:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_592 = lean_array_get_size(x_6);
lean_inc(x_6);
x_593 = l_Array_extract___rarg(x_6, x_588, x_592);
x_594 = lean_unsigned_to_nat(0u);
x_595 = l_Array_empty___closed__1;
x_596 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_589, x_593, x_593, x_594, x_595);
lean_dec(x_593);
lean_dec(x_589);
lean_dec(x_6);
lean_dec(x_2);
x_597 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_596, x_596, x_594, x_590);
lean_dec(x_596);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_591);
return x_598;
}
}
}
case 10:
{
uint8_t x_631; 
lean_dec(x_7);
x_631 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_632 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = x_6;
x_636 = lean_unsigned_to_nat(0u);
x_637 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_637, 0, x_1);
lean_closure_set(x_637, 1, x_2);
lean_closure_set(x_637, 2, x_3);
lean_closure_set(x_637, 3, x_636);
lean_closure_set(x_637, 4, x_635);
x_638 = x_637;
x_639 = lean_apply_5(x_638, x_8, x_9, x_10, x_11, x_634);
if (lean_obj_tag(x_639) == 0)
{
uint8_t x_640; 
x_640 = !lean_is_exclusive(x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; 
x_641 = lean_ctor_get(x_639, 0);
x_642 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_641, x_641, x_636, x_633);
lean_dec(x_641);
lean_ctor_set(x_639, 0, x_642);
return x_639;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_643 = lean_ctor_get(x_639, 0);
x_644 = lean_ctor_get(x_639, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_639);
x_645 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_643, x_643, x_636, x_633);
lean_dec(x_643);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
uint8_t x_647; 
lean_dec(x_633);
x_647 = !lean_is_exclusive(x_639);
if (x_647 == 0)
{
return x_639;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_639, 0);
x_649 = lean_ctor_get(x_639, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_639);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
else
{
uint8_t x_651; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_651 = !lean_is_exclusive(x_632);
if (x_651 == 0)
{
return x_632;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_632, 0);
x_653 = lean_ctor_get(x_632, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_632);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_668; lean_object* x_669; uint8_t x_670; 
lean_dec(x_5);
lean_dec(x_1);
x_655 = lean_ctor_get(x_2, 0);
lean_inc(x_655);
x_656 = lean_array_get_size(x_655);
lean_dec(x_655);
x_657 = lean_ctor_get(x_2, 2);
lean_inc(x_657);
x_668 = lean_nat_add(x_656, x_657);
x_669 = lean_array_get_size(x_6);
x_670 = lean_nat_dec_le(x_669, x_668);
lean_dec(x_669);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_671 = l_Lean_Expr_Inhabited;
x_672 = lean_array_get(x_671, x_6, x_668);
lean_dec(x_668);
x_673 = lean_ctor_get(x_2, 6);
lean_inc(x_673);
x_674 = lean_array_get_size(x_673);
lean_dec(x_673);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_675 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_674, x_672, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_658 = x_676;
x_659 = x_677;
goto block_667;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_2);
x_678 = lean_ctor_get(x_675, 1);
lean_inc(x_678);
lean_dec(x_675);
x_679 = l_Lean_indentExpr(x_4);
x_680 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_681 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_679);
x_682 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_683 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
x_684 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_683, x_8, x_9, x_10, x_11, x_678);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_685 = !lean_is_exclusive(x_684);
if (x_685 == 0)
{
return x_684;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_684, 0);
x_687 = lean_ctor_get(x_684, 1);
lean_inc(x_687);
lean_inc(x_686);
lean_dec(x_684);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
return x_688;
}
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
lean_dec(x_668);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_689 = l_Lean_indentExpr(x_4);
x_690 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_691 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_692 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_693 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
x_694 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_693, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_695 = !lean_is_exclusive(x_694);
if (x_695 == 0)
{
return x_694;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_694, 0);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_inc(x_696);
lean_dec(x_694);
x_698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
return x_698;
}
}
block_667:
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_660 = lean_array_get_size(x_6);
lean_inc(x_6);
x_661 = l_Array_extract___rarg(x_6, x_656, x_660);
x_662 = lean_unsigned_to_nat(0u);
x_663 = l_Array_empty___closed__1;
x_664 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_657, x_661, x_661, x_662, x_663);
lean_dec(x_661);
lean_dec(x_657);
lean_dec(x_6);
lean_dec(x_2);
x_665 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_664, x_664, x_662, x_658);
lean_dec(x_664);
x_666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_659);
return x_666;
}
}
}
case 11:
{
uint8_t x_699; 
lean_dec(x_7);
x_699 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_699 == 0)
{
lean_object* x_700; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_700 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = x_6;
x_704 = lean_unsigned_to_nat(0u);
x_705 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_705, 0, x_1);
lean_closure_set(x_705, 1, x_2);
lean_closure_set(x_705, 2, x_3);
lean_closure_set(x_705, 3, x_704);
lean_closure_set(x_705, 4, x_703);
x_706 = x_705;
x_707 = lean_apply_5(x_706, x_8, x_9, x_10, x_11, x_702);
if (lean_obj_tag(x_707) == 0)
{
uint8_t x_708; 
x_708 = !lean_is_exclusive(x_707);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_707, 0);
x_710 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_709, x_709, x_704, x_701);
lean_dec(x_709);
lean_ctor_set(x_707, 0, x_710);
return x_707;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_711 = lean_ctor_get(x_707, 0);
x_712 = lean_ctor_get(x_707, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_707);
x_713 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_711, x_711, x_704, x_701);
lean_dec(x_711);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_712);
return x_714;
}
}
else
{
uint8_t x_715; 
lean_dec(x_701);
x_715 = !lean_is_exclusive(x_707);
if (x_715 == 0)
{
return x_707;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_707, 0);
x_717 = lean_ctor_get(x_707, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_707);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
}
else
{
uint8_t x_719; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_719 = !lean_is_exclusive(x_700);
if (x_719 == 0)
{
return x_700;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_720 = lean_ctor_get(x_700, 0);
x_721 = lean_ctor_get(x_700, 1);
lean_inc(x_721);
lean_inc(x_720);
lean_dec(x_700);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
return x_722;
}
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_736; lean_object* x_737; uint8_t x_738; 
lean_dec(x_5);
lean_dec(x_1);
x_723 = lean_ctor_get(x_2, 0);
lean_inc(x_723);
x_724 = lean_array_get_size(x_723);
lean_dec(x_723);
x_725 = lean_ctor_get(x_2, 2);
lean_inc(x_725);
x_736 = lean_nat_add(x_724, x_725);
x_737 = lean_array_get_size(x_6);
x_738 = lean_nat_dec_le(x_737, x_736);
lean_dec(x_737);
if (x_738 == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_739 = l_Lean_Expr_Inhabited;
x_740 = lean_array_get(x_739, x_6, x_736);
lean_dec(x_736);
x_741 = lean_ctor_get(x_2, 6);
lean_inc(x_741);
x_742 = lean_array_get_size(x_741);
lean_dec(x_741);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_743 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_742, x_740, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_726 = x_744;
x_727 = x_745;
goto block_735;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
lean_dec(x_725);
lean_dec(x_724);
lean_dec(x_6);
lean_dec(x_2);
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
lean_dec(x_743);
x_747 = l_Lean_indentExpr(x_4);
x_748 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_749 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_747);
x_750 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_751 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
x_752 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_751, x_8, x_9, x_10, x_11, x_746);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_753 = !lean_is_exclusive(x_752);
if (x_753 == 0)
{
return x_752;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_752, 0);
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_752);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; 
lean_dec(x_736);
lean_dec(x_725);
lean_dec(x_724);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_757 = l_Lean_indentExpr(x_4);
x_758 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_759 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
x_760 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_761 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
x_762 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_761, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_763 = !lean_is_exclusive(x_762);
if (x_763 == 0)
{
return x_762;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_762, 0);
x_765 = lean_ctor_get(x_762, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_762);
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
return x_766;
}
}
block_735:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_728 = lean_array_get_size(x_6);
lean_inc(x_6);
x_729 = l_Array_extract___rarg(x_6, x_724, x_728);
x_730 = lean_unsigned_to_nat(0u);
x_731 = l_Array_empty___closed__1;
x_732 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_725, x_729, x_729, x_730, x_731);
lean_dec(x_729);
lean_dec(x_725);
lean_dec(x_6);
lean_dec(x_2);
x_733 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_732, x_732, x_730, x_726);
lean_dec(x_732);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_727);
return x_734;
}
}
}
default: 
{
uint8_t x_767; 
lean_dec(x_7);
x_767 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_767 == 0)
{
lean_object* x_768; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_768 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
x_771 = x_6;
x_772 = lean_unsigned_to_nat(0u);
x_773 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9), 10, 5);
lean_closure_set(x_773, 0, x_1);
lean_closure_set(x_773, 1, x_2);
lean_closure_set(x_773, 2, x_3);
lean_closure_set(x_773, 3, x_772);
lean_closure_set(x_773, 4, x_771);
x_774 = x_773;
x_775 = lean_apply_5(x_774, x_8, x_9, x_10, x_11, x_770);
if (lean_obj_tag(x_775) == 0)
{
uint8_t x_776; 
x_776 = !lean_is_exclusive(x_775);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; 
x_777 = lean_ctor_get(x_775, 0);
x_778 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_777, x_777, x_772, x_769);
lean_dec(x_777);
lean_ctor_set(x_775, 0, x_778);
return x_775;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_779 = lean_ctor_get(x_775, 0);
x_780 = lean_ctor_get(x_775, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_775);
x_781 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_779, x_779, x_772, x_769);
lean_dec(x_779);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
else
{
uint8_t x_783; 
lean_dec(x_769);
x_783 = !lean_is_exclusive(x_775);
if (x_783 == 0)
{
return x_775;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_775, 0);
x_785 = lean_ctor_get(x_775, 1);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_775);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
return x_786;
}
}
}
else
{
uint8_t x_787; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_787 = !lean_is_exclusive(x_768);
if (x_787 == 0)
{
return x_768;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_768, 0);
x_789 = lean_ctor_get(x_768, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_768);
x_790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_790, 0, x_788);
lean_ctor_set(x_790, 1, x_789);
return x_790;
}
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_804; lean_object* x_805; uint8_t x_806; 
lean_dec(x_5);
lean_dec(x_1);
x_791 = lean_ctor_get(x_2, 0);
lean_inc(x_791);
x_792 = lean_array_get_size(x_791);
lean_dec(x_791);
x_793 = lean_ctor_get(x_2, 2);
lean_inc(x_793);
x_804 = lean_nat_add(x_792, x_793);
x_805 = lean_array_get_size(x_6);
x_806 = lean_nat_dec_le(x_805, x_804);
lean_dec(x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_807 = l_Lean_Expr_Inhabited;
x_808 = lean_array_get(x_807, x_6, x_804);
lean_dec(x_804);
x_809 = lean_ctor_get(x_2, 6);
lean_inc(x_809);
x_810 = lean_array_get_size(x_809);
lean_dec(x_809);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_811 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_3, x_810, x_808, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_794 = x_812;
x_795 = x_813;
goto block_803;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; uint8_t x_821; 
lean_dec(x_793);
lean_dec(x_792);
lean_dec(x_6);
lean_dec(x_2);
x_814 = lean_ctor_get(x_811, 1);
lean_inc(x_814);
lean_dec(x_811);
x_815 = l_Lean_indentExpr(x_4);
x_816 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_817 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_815);
x_818 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_819 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
x_820 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_819, x_8, x_9, x_10, x_11, x_814);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_821 = !lean_is_exclusive(x_820);
if (x_821 == 0)
{
return x_820;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_820, 0);
x_823 = lean_ctor_get(x_820, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_820);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; 
lean_dec(x_804);
lean_dec(x_793);
lean_dec(x_792);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_825 = l_Lean_indentExpr(x_4);
x_826 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4;
x_827 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_827, 0, x_826);
lean_ctor_set(x_827, 1, x_825);
x_828 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_829 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_829, 0, x_827);
lean_ctor_set(x_829, 1, x_828);
x_830 = l_Lean_throwError___at_Lean_Elab_mkInhabitantFor___spec__1___rarg(x_829, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_831 = !lean_is_exclusive(x_830);
if (x_831 == 0)
{
return x_830;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_832 = lean_ctor_get(x_830, 0);
x_833 = lean_ctor_get(x_830, 1);
lean_inc(x_833);
lean_inc(x_832);
lean_dec(x_830);
x_834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_834, 0, x_832);
lean_ctor_set(x_834, 1, x_833);
return x_834;
}
}
block_803:
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_796 = lean_array_get_size(x_6);
lean_inc(x_6);
x_797 = l_Array_extract___rarg(x_6, x_792, x_796);
x_798 = lean_unsigned_to_nat(0u);
x_799 = l_Array_empty___closed__1;
x_800 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_2, x_6, x_793, x_797, x_797, x_798, x_799);
lean_dec(x_797);
lean_dec(x_793);
lean_dec(x_6);
lean_dec(x_2);
x_801 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_800, x_800, x_798, x_794);
lean_dec(x_800);
x_802 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_795);
return x_802;
}
}
}
}
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_28__withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to add `below` argument to 'matcher' application");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_indentD(x_1);
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3;
x_4 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkOptionalNode___closed__2;
x_16 = lean_array_push(x_15, x_5);
x_17 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__2(x_16, x_13, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkOptionalNode___closed__2;
x_16 = lean_array_push(x_15, x_5);
x_17 = l_Lean_Meta_mkForallFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__1(x_16, x_13, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_4);
x_10 = l_Lean_Meta_matchMatcherApp_x3f(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_13);
x_15 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_4);
x_19 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3(x_1, x_2, x_3, x_4, x_4, x_16, x_18, x_5, x_6, x_7, x_8, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_110; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
lean_inc(x_4);
x_110 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(x_1, x_4);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = 1;
x_22 = x_111;
goto block_109;
}
else
{
uint8_t x_112; 
x_112 = 0;
x_22 = x_112;
goto block_109;
}
block_109:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_23);
x_25 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_24, x_27);
lean_dec(x_24);
lean_inc(x_3);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg), 7, 2);
lean_closure_set(x_29, 0, x_21);
lean_closure_set(x_29, 1, x_3);
x_30 = lean_st_ref_get(x_8, x_20);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_6, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6(x_1, x_2, x_3, x_4, x_4, x_26, x_28, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_33, x_5, x_6, x_7, x_8, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_37, x_5, x_6, x_7, x_8, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Meta_mapErrorImp___rarg(x_29, x_44, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
x_51 = lean_ctor_get(x_46, 2);
x_52 = lean_ctor_get(x_46, 3);
x_53 = lean_ctor_get(x_46, 4);
x_54 = lean_ctor_get(x_46, 5);
x_55 = lean_ctor_get(x_46, 6);
x_56 = lean_ctor_get(x_46, 7);
x_57 = lean_ctor_get(x_46, 8);
x_58 = l_Array_zip___rarg(x_56, x_55);
lean_dec(x_56);
x_59 = x_58;
x_60 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8), 10, 5);
lean_closure_set(x_60, 0, x_1);
lean_closure_set(x_60, 1, x_2);
lean_closure_set(x_60, 2, x_4);
lean_closure_set(x_60, 3, x_23);
lean_closure_set(x_60, 4, x_59);
x_61 = x_60;
x_62 = lean_apply_5(x_61, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_ctor_set(x_46, 7, x_64);
x_65 = l_Lean_Meta_MatcherApp_toExpr(x_46);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
lean_ctor_set(x_46, 7, x_66);
x_68 = l_Lean_Meta_MatcherApp_toExpr(x_46);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_free_object(x_46);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_46, 0);
x_75 = lean_ctor_get(x_46, 1);
x_76 = lean_ctor_get(x_46, 2);
x_77 = lean_ctor_get(x_46, 3);
x_78 = lean_ctor_get(x_46, 4);
x_79 = lean_ctor_get(x_46, 5);
x_80 = lean_ctor_get(x_46, 6);
x_81 = lean_ctor_get(x_46, 7);
x_82 = lean_ctor_get(x_46, 8);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_46);
x_83 = l_Array_zip___rarg(x_81, x_80);
lean_dec(x_81);
x_84 = x_83;
x_85 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8), 10, 5);
lean_closure_set(x_85, 0, x_1);
lean_closure_set(x_85, 1, x_2);
lean_closure_set(x_85, 2, x_4);
lean_closure_set(x_85, 3, x_23);
lean_closure_set(x_85, 4, x_84);
x_86 = x_85;
x_87 = lean_apply_5(x_86, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
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
x_91 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_75);
lean_ctor_set(x_91, 2, x_76);
lean_ctor_set(x_91, 3, x_77);
lean_ctor_set(x_91, 4, x_78);
lean_ctor_set(x_91, 5, x_79);
lean_ctor_set(x_91, 6, x_80);
lean_ctor_set(x_91, 7, x_88);
lean_ctor_set(x_91, 8, x_82);
x_92 = l_Lean_Meta_MatcherApp_toExpr(x_91);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
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
uint8_t x_98; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_45);
if (x_98 == 0)
{
return x_45;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_45, 0);
x_100 = lean_ctor_get(x_45, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_45);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_21);
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_102);
x_104 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_103);
x_105 = lean_mk_array(x_103, x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_sub(x_103, x_106);
lean_dec(x_103);
lean_inc(x_4);
x_108 = l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11(x_1, x_2, x_3, x_4, x_4, x_105, x_107, x_5, x_6, x_7, x_8, x_20);
return x_108;
}
}
}
}
case 6:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint64_t x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_4, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 2);
lean_inc(x_115);
x_116 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_117 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_114, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = (uint8_t)((x_116 << 24) >> 61);
x_121 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2___boxed), 10, 4);
lean_closure_set(x_121, 0, x_115);
lean_closure_set(x_121, 1, x_1);
lean_closure_set(x_121, 2, x_2);
lean_closure_set(x_121, 3, x_3);
x_122 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__4___rarg(x_113, x_120, x_118, x_121, x_5, x_6, x_7, x_8, x_119);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_117);
if (x_123 == 0)
{
return x_117;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_117, 0);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_117);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
case 7:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_4, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_4, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_4, 2);
lean_inc(x_129);
x_130 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_131 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_128, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = (uint8_t)((x_130 << 24) >> 61);
x_135 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3___boxed), 10, 4);
lean_closure_set(x_135, 0, x_129);
lean_closure_set(x_135, 1, x_1);
lean_closure_set(x_135, 2, x_2);
lean_closure_set(x_135, 3, x_3);
x_136 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__4___rarg(x_127, x_134, x_132, x_135, x_5, x_6, x_7, x_8, x_133);
return x_136;
}
else
{
uint8_t x_137; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_131);
if (x_137 == 0)
{
return x_131;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_131, 0);
x_139 = lean_ctor_get(x_131, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_131);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
case 8:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_4, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_4, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_4, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_4, 3);
lean_inc(x_144);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_145 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_142, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_148 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_143, x_5, x_6, x_7, x_8, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2___boxed), 10, 4);
lean_closure_set(x_151, 0, x_144);
lean_closure_set(x_151, 1, x_1);
lean_closure_set(x_151, 2, x_2);
lean_closure_set(x_151, 3, x_3);
x_152 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12___rarg(x_141, x_146, x_149, x_151, x_5, x_6, x_7, x_8, x_150);
return x_152;
}
else
{
uint8_t x_153; 
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_148);
if (x_153 == 0)
{
return x_148;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_148, 0);
x_155 = lean_ctor_get(x_148, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_148);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_145);
if (x_157 == 0)
{
return x_145;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_145, 0);
x_159 = lean_ctor_get(x_145, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_145);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
case 10:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_4, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_4, 1);
lean_inc(x_162);
lean_dec(x_4);
x_163 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_162, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = l_Lean_mkMData(x_161, x_165);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_163);
x_169 = l_Lean_mkMData(x_161, x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
uint8_t x_171; 
lean_dec(x_161);
x_171 = !lean_is_exclusive(x_163);
if (x_171 == 0)
{
return x_163;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_163, 0);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_163);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
case 11:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_4, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_4, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_4, 2);
lean_inc(x_177);
lean_dec(x_4);
x_178 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_177, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_178) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_178, 0);
x_181 = l_Lean_mkProj(x_175, x_176, x_180);
lean_ctor_set(x_178, 0, x_181);
return x_178;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_178, 0);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_178);
x_184 = l_Lean_mkProj(x_175, x_176, x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_dec(x_176);
lean_dec(x_175);
x_186 = !lean_is_exclusive(x_178);
if (x_186 == 0)
{
return x_178;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_178, 0);
x_188 = lean_ctor_get(x_178, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_178);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
default: 
{
lean_object* x_190; 
lean_dec(x_3);
lean_dec(x_2);
x_190 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_190;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = l_Array_shrink___main___rarg(x_3, x_5);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_3, x_4);
x_10 = lean_expr_eqv(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 7);
x_12 = l_Array_contains___at_Lean_Meta_addInstanceEntry___spec__11(x_11, x_9);
lean_dec(x_9);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_16 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_fswap(x_3, x_4, x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_21 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_3 = x_18;
x_4 = x_20;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_4 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_4 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_getLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_4__getLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_decLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l___private_Lean_Meta_LevelDefEq_2__decLevelImp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__3;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_decLevel___rarg___lambda__1___closed__6;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
lean_inc(x_10);
x_18 = l_Array_extract___rarg(x_10, x_17, x_1);
x_19 = l_Lean_Expr_Inhabited;
x_20 = lean_array_get(x_19, x_10, x_1);
x_21 = lean_array_get(x_19, x_10, x_2);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_add(x_1, x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_10);
lean_inc(x_10);
x_25 = l_Array_extract___rarg(x_10, x_23, x_24);
x_26 = l_Lean_Expr_replaceFVars(x_3, x_4, x_18);
lean_dec(x_18);
x_27 = l_Lean_Expr_replaceFVar(x_26, x_5, x_20);
lean_dec(x_20);
lean_dec(x_26);
x_28 = l_Lean_Expr_replaceFVars(x_27, x_6, x_25);
lean_dec(x_25);
lean_dec(x_27);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_7, x_8, x_21, x_28, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__2(x_10, x_30, x_12, x_13, x_14, x_15, x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_mkApp(x_9, x_34);
x_36 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_6, x_6, x_17, x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = l_Lean_mkApp(x_9, x_37);
x_40 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_6, x_6, x_17, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_Inhabited;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_8, x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_21, x_22);
x_24 = lean_nat_add(x_23, x_22);
x_25 = lean_array_get_size(x_2);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1___boxed), 16, 9);
lean_closure_set(x_28, 0, x_21);
lean_closure_set(x_28, 1, x_23);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_1);
lean_closure_set(x_28, 4, x_4);
lean_closure_set(x_28, 5, x_2);
lean_closure_set(x_28, 6, x_5);
lean_closure_set(x_28, 7, x_6);
lean_closure_set(x_28, 8, x_7);
x_29 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(x_19, x_27, x_28, x_10, x_11, x_12, x_13, x_20);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOnType ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn     ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn motive: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn univ: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_headBeta(x_10);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = l_Lean_Expr_Inhabited;
x_16 = lean_array_get(x_15, x_13, x_14);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1(x_2, x_16, x_13, x_17, x_17);
lean_inc(x_4);
lean_inc(x_18);
x_19 = l_Lean_Meta_mkForallFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__1(x_18, x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_20);
x_22 = l___private_Lean_Meta_InferType_4__getLevelImp(x_20, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_285; lean_object* x_286; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_296 = lean_st_ref_get(x_7, x_24);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_297, 3);
lean_inc(x_298);
lean_dec(x_297);
x_299 = lean_ctor_get_uint8(x_298, sizeof(void*)*1);
lean_dec(x_298);
if (x_299 == 0)
{
lean_object* x_300; uint8_t x_301; 
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
lean_dec(x_296);
x_301 = 0;
x_285 = x_301;
x_286 = x_300;
goto block_295;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_302 = lean_ctor_get(x_296, 1);
lean_inc(x_302);
lean_dec(x_296);
x_303 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_304 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_303, x_4, x_5, x_6, x_7, x_302);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_unbox(x_305);
lean_dec(x_305);
x_285 = x_307;
x_286 = x_306;
goto block_295;
}
block_284:
{
uint8_t x_26; uint8_t x_27; 
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
if (x_26 == 0)
{
uint8_t x_281; 
x_281 = 0;
x_27 = x_281;
goto block_280;
}
else
{
lean_object* x_282; uint8_t x_283; 
x_282 = l_Lean_levelZero;
x_283 = lean_level_eq(x_23, x_282);
x_27 = x_283;
goto block_280;
}
block_280:
{
uint8_t x_28; 
if (x_26 == 0)
{
uint8_t x_275; 
x_275 = 0;
x_28 = x_275;
goto block_274;
}
else
{
lean_object* x_276; uint8_t x_277; 
x_276 = l_Lean_levelZero;
x_277 = lean_level_eq(x_23, x_276);
if (x_277 == 0)
{
uint8_t x_278; 
x_278 = 1;
x_28 = x_278;
goto block_274;
}
else
{
uint8_t x_279; 
x_279 = 0;
x_28 = x_279;
goto block_274;
}
}
block_274:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 7);
lean_inc(x_29);
lean_inc(x_16);
lean_inc(x_29);
x_30 = lean_array_push(x_29, x_16);
lean_inc(x_4);
x_31 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__2(x_30, x_20, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_121; lean_object* x_122; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_132 = lean_st_ref_get(x_7, x_33);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 3);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_ctor_get_uint8(x_134, sizeof(void*)*1);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
lean_dec(x_132);
x_137 = 0;
x_121 = x_137;
x_122 = x_136;
goto block_131;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_dec(x_132);
x_139 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_140 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_139, x_4, x_5, x_6, x_7, x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_unbox(x_141);
lean_dec(x_141);
x_121 = x_143;
x_122 = x_142;
goto block_131;
}
block_120:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_2, 6);
lean_inc(x_35);
if (x_27 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_2, 4);
lean_inc(x_109);
x_110 = l_Lean_Meta_brecOnSuffix;
x_111 = lean_name_mk_string(x_109, x_110);
x_112 = lean_ctor_get(x_2, 5);
lean_inc(x_112);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_23);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_mkConst(x_111, x_113);
x_36 = x_114;
goto block_108;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_23);
x_115 = lean_ctor_get(x_2, 4);
lean_inc(x_115);
x_116 = l_Lean_Meta_binductionOnSuffix;
x_117 = lean_name_mk_string(x_115, x_116);
x_118 = lean_ctor_get(x_2, 5);
lean_inc(x_118);
x_119 = l_Lean_mkConst(x_117, x_118);
x_36 = x_119;
goto block_108;
}
block_108:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_35, x_35, x_17, x_36);
lean_dec(x_35);
x_38 = l_Lean_mkApp(x_37, x_32);
x_39 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_29, x_29, x_17, x_38);
lean_inc(x_16);
x_40 = l_Lean_mkApp(x_39, x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_40);
x_41 = l_Lean_Meta_check(x_40, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_40);
x_43 = l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_40, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_63; uint8_t x_77; lean_object* x_78; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_88 = lean_st_ref_get(x_7, x_45);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 3);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_ctor_get_uint8(x_90, sizeof(void*)*1);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = 0;
x_77 = x_93;
x_78 = x_92;
goto block_87;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
x_95 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_96 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_95, x_4, x_5, x_6, x_7, x_94);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_unbox(x_97);
lean_dec(x_97);
x_77 = x_99;
x_78 = x_98;
goto block_87;
}
block_62:
{
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed), 14, 7);
lean_closure_set(x_48, 0, x_29);
lean_closure_set(x_48, 1, x_18);
lean_closure_set(x_48, 2, x_3);
lean_closure_set(x_48, 3, x_16);
lean_closure_set(x_48, 4, x_1);
lean_closure_set(x_48, 5, x_2);
lean_closure_set(x_48, 6, x_40);
x_49 = l___private_Lean_Meta_Match_Match_42__updateAlts___main___lambda__2___closed__1;
x_50 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(x_44, x_49, x_48, x_4, x_5, x_6, x_7, x_47);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_inc(x_44);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_44);
x_52 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_57 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_56, x_55, x_4, x_5, x_6, x_7, x_47);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed), 14, 7);
lean_closure_set(x_59, 0, x_29);
lean_closure_set(x_59, 1, x_18);
lean_closure_set(x_59, 2, x_3);
lean_closure_set(x_59, 3, x_16);
lean_closure_set(x_59, 4, x_1);
lean_closure_set(x_59, 5, x_2);
lean_closure_set(x_59, 6, x_40);
x_60 = l___private_Lean_Meta_Match_Match_42__updateAlts___main___lambda__2___closed__1;
x_61 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(x_44, x_60, x_59, x_4, x_5, x_6, x_7, x_58);
return x_61;
}
}
block_76:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_st_ref_get(x_7, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 3);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = 0;
x_46 = x_69;
x_47 = x_68;
goto block_62;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_72 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_71, x_4, x_5, x_6, x_7, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_46 = x_75;
x_47 = x_74;
goto block_62;
}
}
block_87:
{
if (x_77 == 0)
{
x_63 = x_78;
goto block_76;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_40);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_40);
x_80 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__4;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_85 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_84, x_83, x_4, x_5, x_6, x_7, x_78);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_63 = x_86;
goto block_76;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_43);
if (x_100 == 0)
{
return x_43;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_43, 0);
x_102 = lean_ctor_get(x_43, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_43);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_41);
if (x_104 == 0)
{
return x_41;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_41, 0);
x_106 = lean_ctor_get(x_41, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_41);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
block_131:
{
if (x_121 == 0)
{
x_34 = x_122;
goto block_120;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_inc(x_32);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_32);
x_124 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__6;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_129 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_128, x_127, x_4, x_5, x_6, x_7, x_122);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_34 = x_130;
goto block_120;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_31);
if (x_144 == 0)
{
return x_31;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_31, 0);
x_146 = lean_ctor_get(x_31, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_31);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; 
x_148 = l_Lean_Meta_decLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__3(x_23, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_2, 7);
lean_inc(x_151);
lean_inc(x_16);
lean_inc(x_151);
x_152 = lean_array_push(x_151, x_16);
lean_inc(x_4);
x_153 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__2(x_152, x_20, x_4, x_5, x_6, x_7, x_150);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_243; lean_object* x_244; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_254 = lean_st_ref_get(x_7, x_155);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_255, 3);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_ctor_get_uint8(x_256, sizeof(void*)*1);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_254, 1);
lean_inc(x_258);
lean_dec(x_254);
x_259 = 0;
x_243 = x_259;
x_244 = x_258;
goto block_253;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_260 = lean_ctor_get(x_254, 1);
lean_inc(x_260);
lean_dec(x_254);
x_261 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_262 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_261, x_4, x_5, x_6, x_7, x_260);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_unbox(x_263);
lean_dec(x_263);
x_243 = x_265;
x_244 = x_264;
goto block_253;
}
block_242:
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_2, 6);
lean_inc(x_157);
if (x_27 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_231 = lean_ctor_get(x_2, 4);
lean_inc(x_231);
x_232 = l_Lean_Meta_brecOnSuffix;
x_233 = lean_name_mk_string(x_231, x_232);
x_234 = lean_ctor_get(x_2, 5);
lean_inc(x_234);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_149);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Lean_mkConst(x_233, x_235);
x_158 = x_236;
goto block_230;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_149);
x_237 = lean_ctor_get(x_2, 4);
lean_inc(x_237);
x_238 = l_Lean_Meta_binductionOnSuffix;
x_239 = lean_name_mk_string(x_237, x_238);
x_240 = lean_ctor_get(x_2, 5);
lean_inc(x_240);
x_241 = l_Lean_mkConst(x_239, x_240);
x_158 = x_241;
goto block_230;
}
block_230:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_157, x_157, x_17, x_158);
lean_dec(x_157);
x_160 = l_Lean_mkApp(x_159, x_154);
x_161 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_151, x_151, x_17, x_160);
lean_inc(x_16);
x_162 = l_Lean_mkApp(x_161, x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_162);
x_163 = l_Lean_Meta_check(x_162, x_4, x_5, x_6, x_7, x_156);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_162);
x_165 = l_Lean_Meta_inferType___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_findAssumption_x3f___spec__1(x_162, x_4, x_5, x_6, x_7, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_185; uint8_t x_199; lean_object* x_200; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_210 = lean_st_ref_get(x_7, x_167);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 3);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_ctor_get_uint8(x_212, sizeof(void*)*1);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_dec(x_210);
x_215 = 0;
x_199 = x_215;
x_200 = x_214;
goto block_209;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
lean_dec(x_210);
x_217 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_218 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_217, x_4, x_5, x_6, x_7, x_216);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_unbox(x_219);
lean_dec(x_219);
x_199 = x_221;
x_200 = x_220;
goto block_209;
}
block_184:
{
if (x_168 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed), 14, 7);
lean_closure_set(x_170, 0, x_151);
lean_closure_set(x_170, 1, x_18);
lean_closure_set(x_170, 2, x_3);
lean_closure_set(x_170, 3, x_16);
lean_closure_set(x_170, 4, x_1);
lean_closure_set(x_170, 5, x_2);
lean_closure_set(x_170, 6, x_162);
x_171 = l___private_Lean_Meta_Match_Match_42__updateAlts___main___lambda__2___closed__1;
x_172 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(x_166, x_171, x_170, x_4, x_5, x_6, x_7, x_169);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_inc(x_166);
x_173 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_173, 0, x_166);
x_174 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2;
x_175 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_177 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_179 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_178, x_177, x_4, x_5, x_6, x_7, x_169);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed), 14, 7);
lean_closure_set(x_181, 0, x_151);
lean_closure_set(x_181, 1, x_18);
lean_closure_set(x_181, 2, x_3);
lean_closure_set(x_181, 3, x_16);
lean_closure_set(x_181, 4, x_1);
lean_closure_set(x_181, 5, x_2);
lean_closure_set(x_181, 6, x_162);
x_182 = l___private_Lean_Meta_Match_Match_42__updateAlts___main___lambda__2___closed__1;
x_183 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__2___rarg(x_166, x_182, x_181, x_4, x_5, x_6, x_7, x_180);
return x_183;
}
}
block_198:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_st_ref_get(x_7, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 3);
lean_inc(x_188);
lean_dec(x_187);
x_189 = lean_ctor_get_uint8(x_188, sizeof(void*)*1);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_dec(x_186);
x_191 = 0;
x_168 = x_191;
x_169 = x_190;
goto block_184;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_192 = lean_ctor_get(x_186, 1);
lean_inc(x_192);
lean_dec(x_186);
x_193 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_194 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_193, x_4, x_5, x_6, x_7, x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_unbox(x_195);
lean_dec(x_195);
x_168 = x_197;
x_169 = x_196;
goto block_184;
}
}
block_209:
{
if (x_199 == 0)
{
x_185 = x_200;
goto block_198;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_inc(x_162);
x_201 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_201, 0, x_162);
x_202 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__4;
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_207 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_206, x_205, x_4, x_5, x_6, x_7, x_200);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_185 = x_208;
goto block_198;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_162);
lean_dec(x_151);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_165);
if (x_222 == 0)
{
return x_165;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_165, 0);
x_224 = lean_ctor_get(x_165, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_165);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_162);
lean_dec(x_151);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_163);
if (x_226 == 0)
{
return x_163;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_163, 0);
x_228 = lean_ctor_get(x_163, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_163);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
block_253:
{
if (x_243 == 0)
{
x_156 = x_244;
goto block_242;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_inc(x_154);
x_245 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_245, 0, x_154);
x_246 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__6;
x_247 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_249 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_251 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_250, x_249, x_4, x_5, x_6, x_7, x_244);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_156 = x_252;
goto block_242;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_153);
if (x_266 == 0)
{
return x_153;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_153, 0);
x_268 = lean_ctor_get(x_153, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_153);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_148);
if (x_270 == 0)
{
return x_148;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_148, 0);
x_272 = lean_ctor_get(x_148, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_148);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
}
block_295:
{
if (x_285 == 0)
{
x_25 = x_286;
goto block_284;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_inc(x_23);
x_287 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_287, 0, x_23);
x_288 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__8;
x_289 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
x_290 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_291 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_293 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_292, x_291, x_4, x_5, x_6, x_7, x_286);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
x_25 = x_294;
goto block_284;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_22);
if (x_308 == 0)
{
return x_22;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_22, 0);
x_310 = lean_ctor_get(x_22, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_22);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_19);
if (x_312 == 0)
{
return x_19;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_19, 0);
x_314 = lean_ctor_get(x_19, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_19);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
else
{
uint8_t x_316; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_316 = !lean_is_exclusive(x_9);
if (x_316 == 0)
{
return x_9;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_9, 0);
x_318 = lean_ctor_get(x_9, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_9);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_decLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_decLevel___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn(x_1, x_6, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
x_15 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkFnInhabitant_x3f_loop___spec__2(x_3, x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_68 = lean_st_ref_get(x_10, x_17);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get_uint8(x_70, sizeof(void*)*1);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = 0;
x_18 = x_73;
x_19 = x_72;
goto block_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
lean_inc(x_5);
x_75 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_5, x_7, x_8, x_9, x_10, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_18 = x_78;
x_19 = x_77;
goto block_67;
}
block_67:
{
if (x_18 == 0)
{
lean_object* x_20; 
lean_dec(x_5);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(x_1, x_16, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
x_26 = lean_ctor_get(x_4, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_1);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_23);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
x_33 = lean_ctor_get(x_4, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_34 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_1);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_16);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_16);
x_41 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_5, x_44, x_7, x_8, x_9, x_10, x_19);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_1);
x_47 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(x_1, x_16, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_51 = lean_ctor_get(x_4, 0);
x_52 = lean_ctor_get(x_4, 1);
x_53 = lean_ctor_get(x_4, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_54 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_1);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*5, x_50);
lean_ctor_set(x_47, 0, x_54);
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_ctor_get(x_4, 1);
x_60 = lean_ctor_get(x_4, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_61 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_1);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_55);
lean_ctor_set_uint8(x_61, sizeof(void*)*5, x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_1);
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
}
else
{
uint8_t x_79; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
return x_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_15, 0);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_12);
if (x_83 == 0)
{
return x_12;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_12, 0);
x_85 = lean_ctor_get(x_12, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_12);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Iterator_HasRepr___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :=\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
x_9 = l_Lean_Elab_addAsAxiom(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_18; lean_object* x_19; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_39 = lean_st_ref_get(x_7, x_10);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_18 = x_44;
x_19 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_47 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__3(x_46, x_4, x_5, x_6, x_7, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox(x_48);
lean_dec(x_48);
x_18 = x_50;
x_19 = x_49;
goto block_38;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix(x_12, x_2, x_3);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___boxed), 11, 5);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_14);
lean_inc(x_13);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_13, x_2, x_15, x_13, x_4, x_5, x_6, x_7, x_11);
return x_16;
}
block_38:
{
if (x_18 == 0)
{
x_11 = x_19;
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___closed__13;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_toList___rarg(x_2);
x_27 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_26);
x_28 = l_Lean_MessageData_ofList(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_3);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_3);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
x_35 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_36 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___spec__2(x_35, x_34, x_4, x_5, x_6, x_7, x_19);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_11 = x_37;
goto block_17;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_9);
if (x_51 == 0)
{
return x_9;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7___rarg(x_7, x_8, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_12, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_12, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_structuralRecursion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural recursion does not handle mutually recursive functions");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_structuralRecursion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_structuralRecursion___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_structuralRecursion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_structuralRecursion___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_structuralRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_array_get_size(x_1);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 1;
x_9 = x_34;
goto block_30;
}
else
{
uint8_t x_35; 
x_35 = 0;
x_9 = x_35;
goto block_30;
}
block_30:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Elab_PreDefinition_inhabited;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_1, x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion(x_12, x_4, x_5, x_6, x_7, x_8);
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
lean_inc(x_2);
x_17 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_addAndCompileUnsafeRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = l_Lean_Elab_structuralRecursion___closed__3;
x_29 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
}
}
}
lean_object* l_Lean_Elab_structuralRecursion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_structuralRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_3362_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(lean_object*);
lean_object* initialize_Lean_Meta_ForEachExpr(lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_PreDefinition_Structural(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ForEachExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__9);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__11);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__13 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__13);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__15 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__15);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__17 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__17);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__9);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__11);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__13 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__13);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__14);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__15 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__15);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__16 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__16);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__1);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___lambda__2___closed__2);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__1);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__2 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__3___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__3 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__3);
l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__4);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__4 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__4);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__5 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__5);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__6 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__6);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__7 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__7();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__7);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__8 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__8();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___lambda__1___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__3);
l_Lean_Elab_structuralRecursion___closed__1 = _init_l_Lean_Elab_structuralRecursion___closed__1();
lean_mark_persistent(l_Lean_Elab_structuralRecursion___closed__1);
l_Lean_Elab_structuralRecursion___closed__2 = _init_l_Lean_Elab_structuralRecursion___closed__2();
lean_mark_persistent(l_Lean_Elab_structuralRecursion___closed__2);
l_Lean_Elab_structuralRecursion___closed__3 = _init_l_Lean_Elab_structuralRecursion___closed__3();
lean_mark_persistent(l_Lean_Elab_structuralRecursion___closed__3);
res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_3362_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
