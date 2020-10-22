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
extern lean_object* l_Lean_Meta_binductionOnSuffix;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__2;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__2(lean_object*);
uint8_t l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__1;
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__1;
uint8_t l_Array_contains___at_Lean_Meta_addInstanceEntry___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__6___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__3(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__1(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2;
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__16;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__6;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__1(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafeRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_PreDefinition_inhabited;
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__7;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__6;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__17;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__2;
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__9;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix_match__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
extern lean_object* l_Lean_Meta_brecOnSuffix;
lean_object* l_Std_HashMapImp_insert___at_Lean_Meta_ForEachExpr_visit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExprImp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__7;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1;
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__4(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__7;
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__3___rarg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__7(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__3(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14;
lean_object* l_Lean_Meta_forEachExpr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5;
lean_object* l_Lean_Elab_structuralRecursion___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__5;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__14;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__15;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2;
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__2;
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_processAssignmentFOApprox_loop___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__2(lean_object*);
uint8_t l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_3445_(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__5;
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__3___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__8;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__4(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__3;
lean_object* l_List_map___main___at_Lean_MessageData_Lean_Message___instance__12___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__6;
lean_object* l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_912____spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__4;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__4;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1;
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dependsOn___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__13;
lean_object* l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__2;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__1;
extern lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__1;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__1(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__15;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__3;
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos_match__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2;
lean_object* l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__9;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10;
lean_object* l_Lean_Meta_forEachExpr___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__8;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__5;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__2___rarg___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f_match__3(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__2(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__4;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn___lambda__1___closed__2;
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__11;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_662____closed__2;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__13;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__11;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f_match__3(lean_object*);
lean_object* l_Array_isPrefixOfAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux_match__3(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_27; lean_object* x_28; lean_object* x_115; 
x_115 = lean_st_ref_get(x_4, x_6);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__7(x_117, x_3);
lean_dec(x_117);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
lean_free_object(x_115);
x_120 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = 1;
x_27 = x_121;
x_28 = x_118;
goto block_114;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_Expr_getAppNumArgsAux(x_3, x_122);
x_124 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_123);
x_125 = lean_mk_array(x_123, x_124);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_123, x_126);
lean_dec(x_123);
lean_inc(x_3);
x_128 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_125, x_127);
x_129 = lean_st_ref_take(x_5, x_118);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_array_get_size(x_128);
x_133 = lean_nat_dec_lt(x_132, x_130);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_132);
x_134 = lean_st_ref_set(x_5, x_130, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_128, x_2);
lean_dec(x_128);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = 1;
x_27 = x_137;
x_28 = x_135;
goto block_114;
}
else
{
uint8_t x_138; 
x_138 = 0;
x_27 = x_138;
x_28 = x_135;
goto block_114;
}
}
else
{
uint8_t x_139; 
lean_dec(x_128);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_134);
if (x_139 == 0)
{
return x_134;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_134, 0);
x_141 = lean_ctor_get(x_134, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_134);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; 
lean_dec(x_130);
x_143 = lean_st_ref_set(x_5, x_132, x_131);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_128, x_2);
lean_dec(x_128);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = 1;
x_27 = x_146;
x_28 = x_144;
goto block_114;
}
else
{
uint8_t x_147; 
x_147 = 0;
x_27 = x_147;
x_28 = x_144;
goto block_114;
}
}
else
{
uint8_t x_148; 
lean_dec(x_128);
lean_dec(x_3);
x_148 = !lean_is_exclusive(x_143);
if (x_148 == 0)
{
return x_143;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_143, 0);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_143);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_128);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_129);
if (x_152 == 0)
{
return x_129;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_129, 0);
x_154 = lean_ctor_get(x_129, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_129);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_156; 
lean_dec(x_3);
x_156 = lean_ctor_get(x_119, 0);
lean_inc(x_156);
lean_dec(x_119);
lean_ctor_set(x_115, 0, x_156);
return x_115;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_115, 0);
x_158 = lean_ctor_get(x_115, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_115);
x_159 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_ForEachExpr_visit___spec__7(x_157, x_3);
lean_dec(x_157);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = 1;
x_27 = x_161;
x_28 = x_158;
goto block_114;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_Lean_Expr_getAppNumArgsAux(x_3, x_162);
x_164 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_163);
x_165 = lean_mk_array(x_163, x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_163, x_166);
lean_dec(x_163);
lean_inc(x_3);
x_168 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_165, x_167);
x_169 = lean_st_ref_take(x_5, x_158);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_array_get_size(x_168);
x_173 = lean_nat_dec_lt(x_172, x_170);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_172);
x_174 = lean_st_ref_set(x_5, x_170, x_171);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_168, x_2);
lean_dec(x_168);
if (x_176 == 0)
{
uint8_t x_177; 
x_177 = 1;
x_27 = x_177;
x_28 = x_175;
goto block_114;
}
else
{
uint8_t x_178; 
x_178 = 0;
x_27 = x_178;
x_28 = x_175;
goto block_114;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_168);
lean_dec(x_3);
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_174, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; 
lean_dec(x_170);
x_183 = lean_st_ref_set(x_5, x_172, x_171);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Array_isPrefixOf___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__1(x_168, x_2);
lean_dec(x_168);
if (x_185 == 0)
{
uint8_t x_186; 
x_186 = 1;
x_27 = x_186;
x_28 = x_184;
goto block_114;
}
else
{
uint8_t x_187; 
x_187 = 0;
x_27 = x_187;
x_28 = x_184;
goto block_114;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_168);
lean_dec(x_3);
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_190 = x_183;
} else {
 lean_dec_ref(x_183);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_168);
lean_dec(x_3);
x_192 = lean_ctor_get(x_169, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_169, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_194 = x_169;
} else {
 lean_dec_ref(x_169);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_3);
x_196 = lean_ctor_get(x_159, 0);
lean_inc(x_196);
lean_dec(x_159);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_158);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_3);
x_198 = !lean_is_exclusive(x_115);
if (x_198 == 0)
{
return x_115;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_115, 0);
x_200 = lean_ctor_get(x_115, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_115);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
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
x_12 = l_Std_HashMapImp_insert___at_Lean_Meta_ForEachExpr_visit___spec__1(x_10, x_3, x_7);
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
lean_object* x_29; 
x_29 = lean_box(0);
x_7 = x_29;
x_8 = x_28;
goto block_26;
}
else
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
x_32 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_30, x_4, x_5, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_31, x_4, x_5, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_7 = x_35;
x_8 = x_36;
goto block_26;
}
else
{
uint8_t x_37; 
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
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
lean_dec(x_31);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
x_47 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_45, x_4, x_5, x_28);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_46, x_4, x_5, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_7 = x_50;
x_8 = x_51;
goto block_26;
}
else
{
uint8_t x_52; 
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
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
lean_dec(x_46);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 7:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 2);
lean_inc(x_61);
x_62 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_60, x_4, x_5, x_28);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_61, x_4, x_5, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_7 = x_65;
x_8 = x_66;
goto block_26;
}
else
{
uint8_t x_67; 
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_64);
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
lean_dec(x_61);
lean_dec(x_3);
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
case 8:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
x_78 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_75, x_4, x_5, x_28);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_76, x_4, x_5, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_77, x_4, x_5, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_7 = x_83;
x_8 = x_84;
goto block_26;
}
else
{
uint8_t x_85; 
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_82);
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
lean_dec(x_77);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_80);
if (x_89 == 0)
{
return x_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_80);
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
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_78);
if (x_93 == 0)
{
return x_78;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_78, 0);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_78);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
case 10:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_3, 1);
lean_inc(x_97);
x_98 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_97, x_4, x_5, x_28);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_7 = x_99;
x_8 = x_100;
goto block_26;
}
else
{
uint8_t x_101; 
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_98);
if (x_101 == 0)
{
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
case 11:
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_3, 2);
lean_inc(x_105);
x_106 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_105, x_4, x_5, x_28);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_7 = x_107;
x_8 = x_108;
goto block_26;
}
else
{
uint8_t x_109; 
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
default: 
{
lean_object* x_113; 
x_113 = lean_box(0);
x_7 = x_113;
x_8 = x_28;
goto block_26;
}
}
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
x_13 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_3, x_11, x_7, x_12);
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
lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ForEachExpr_visit___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_9 = l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_7, x_8);
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
x_20 = l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__6___spec__2___rarg(x_18, x_19, x_9, x_10, x_11, x_12, x_13);
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
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1), 6, 1);
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
x_18 = l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__6___spec__2___rarg(x_16, x_17, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
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
x_19 = l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__6___spec__2___rarg(x_17, x_18, x_8, x_9, x_10, x_11, x_12);
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
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1), 6, 1);
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
x_17 = l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__6___spec__2___rarg(x_15, x_16, x_7, x_8, x_9, x_10, x_11);
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
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___closed__4;
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
x_7 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_912____spec__1___rarg(x_6, x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PreDefinition.Structural");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.Structural.0.Lean.Elab.findRecArg.loop");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__1;
x_2 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(111u);
x_4 = lean_unsigned_to_nat(117u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Array_indexOfAux___main___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__1(x_1, x_10, x_8);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Nat_Inhabited;
x_15 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__3;
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
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(x_1, x_6, x_2, lean_box(0));
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
x_14 = l_Lean_Meta_getFVarLocalDecl___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstanceImp___spec__1(x_13, x_5, x_6, x_7, x_8, x_9);
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
x_19 = l_Lean_Meta_whnfD___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__1(x_18, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_getAppFn(x_20);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
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
x_39 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(x_38, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_10);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_4, x_43);
lean_dec(x_4);
x_4 = x_44;
x_9 = x_42;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = l_Lean_Meta_binductionOnSuffix;
lean_inc(x_36);
x_48 = lean_name_mk_string(x_36, x_47);
x_49 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(x_48, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get_uint8(x_34, sizeof(void*)*5 + 2);
if (x_52 == 0)
{
lean_object* x_427; 
lean_dec(x_50);
x_427 = lean_box(0);
x_53 = x_427;
goto block_426;
}
else
{
uint8_t x_428; 
x_428 = lean_unbox(x_50);
lean_dec(x_50);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_10);
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_add(x_4, x_429);
lean_dec(x_4);
x_4 = x_430;
x_9 = x_51;
goto _start;
}
else
{
lean_object* x_432; 
x_432 = lean_box(0);
x_53 = x_432;
goto block_426;
}
}
block_426:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_297; uint8_t x_298; 
lean_dec(x_53);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Expr_getAppNumArgsAux(x_20, x_54);
x_56 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_55);
x_57 = lean_mk_array(x_55, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
lean_inc(x_20);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_20, x_57, x_59);
x_61 = lean_ctor_get(x_34, 1);
lean_inc(x_61);
lean_inc(x_61);
lean_inc(x_60);
x_62 = l_Array_extract___rarg(x_60, x_54, x_61);
x_63 = lean_array_get_size(x_60);
x_64 = l_Array_extract___rarg(x_60, x_61, x_63);
x_297 = lean_array_get_size(x_64);
x_298 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(x_20, x_34, x_64, x_297, x_54);
lean_dec(x_297);
lean_dec(x_34);
if (x_298 == 0)
{
uint8_t x_299; 
x_299 = l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(x_64, x_54);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_10);
x_300 = lean_nat_add(x_4, x_58);
lean_dec(x_4);
lean_inc(x_300);
x_301 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_300);
x_302 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_303 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_304 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
x_305 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__16;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_Lean_indentExpr(x_20);
x_308 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_st_ref_get(x_8, x_51);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_st_ref_get(x_6, x_313);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_310, x_5, x_6, x_7, x_8, x_317);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_314, x_5, x_6, x_7, x_8, x_321);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_324 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_318, x_5, x_6, x_7, x_8, x_323);
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_ctor_get(x_320, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_320, 1);
lean_inc(x_327);
lean_dec(x_320);
x_328 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_300, x_5, x_6, x_7, x_8, x_325);
if (lean_obj_tag(x_328) == 0)
{
uint8_t x_329; 
lean_dec(x_327);
lean_dec(x_326);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
return x_328;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_328, 0);
x_331 = lean_ctor_get(x_328, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_328);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
else
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_328, 0);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
uint8_t x_334; 
x_334 = !lean_is_exclusive(x_328);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_ctor_get(x_328, 0);
lean_dec(x_335);
x_336 = !lean_is_exclusive(x_333);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_337 = lean_ctor_get(x_333, 1);
x_338 = lean_ctor_get(x_333, 0);
lean_dec(x_338);
x_339 = l_Lean_MessageData_ofList___closed__3;
x_340 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_340, 0, x_327);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
x_342 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_337);
lean_ctor_set(x_333, 1, x_342);
lean_ctor_set(x_333, 0, x_326);
return x_328;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_ctor_get(x_333, 1);
lean_inc(x_343);
lean_dec(x_333);
x_344 = l_Lean_MessageData_ofList___closed__3;
x_345 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_345, 0, x_327);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
x_347 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_343);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_326);
lean_ctor_set(x_348, 1, x_347);
lean_ctor_set(x_328, 0, x_348);
return x_328;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_349 = lean_ctor_get(x_328, 1);
lean_inc(x_349);
lean_dec(x_328);
x_350 = lean_ctor_get(x_333, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_351 = x_333;
} else {
 lean_dec_ref(x_333);
 x_351 = lean_box(0);
}
x_352 = l_Lean_MessageData_ofList___closed__3;
x_353 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_353, 0, x_327);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_350);
if (lean_is_scalar(x_351)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_351;
}
lean_ctor_set(x_356, 0, x_326);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_349);
return x_357;
}
}
else
{
uint8_t x_358; 
lean_dec(x_327);
lean_dec(x_326);
x_358 = !lean_is_exclusive(x_328);
if (x_358 == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_328, 0);
lean_dec(x_359);
return x_328;
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_328, 1);
lean_inc(x_360);
lean_dec(x_328);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_333);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
}
else
{
lean_object* x_362; uint8_t x_363; 
x_362 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_getIndexMinPos(x_2, x_64);
x_363 = lean_nat_dec_lt(x_362, x_1);
if (x_363 == 0)
{
lean_dec(x_362);
lean_inc(x_1);
x_65 = x_1;
goto block_296;
}
else
{
x_65 = x_362;
goto block_296;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_10);
x_364 = lean_nat_add(x_4, x_58);
lean_dec(x_4);
lean_inc(x_364);
x_365 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_364);
x_366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_366, 0, x_365);
x_367 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_368 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__18;
x_370 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = l_Lean_indentExpr(x_20);
x_372 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_374 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_st_ref_get(x_8, x_51);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_ctor_get(x_376, 0);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_st_ref_get(x_6, x_377);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_ctor_get(x_380, 0);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_374, x_5, x_6, x_7, x_8, x_381);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_378, x_5, x_6, x_7, x_8, x_385);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
lean_dec(x_386);
x_388 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_382, x_5, x_6, x_7, x_8, x_387);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
lean_dec(x_388);
x_390 = lean_ctor_get(x_384, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_384, 1);
lean_inc(x_391);
lean_dec(x_384);
x_392 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_364, x_5, x_6, x_7, x_8, x_389);
if (lean_obj_tag(x_392) == 0)
{
uint8_t x_393; 
lean_dec(x_391);
lean_dec(x_390);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
return x_392;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_392, 0);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_392);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
else
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_392, 0);
lean_inc(x_397);
if (lean_obj_tag(x_397) == 0)
{
uint8_t x_398; 
x_398 = !lean_is_exclusive(x_392);
if (x_398 == 0)
{
lean_object* x_399; uint8_t x_400; 
x_399 = lean_ctor_get(x_392, 0);
lean_dec(x_399);
x_400 = !lean_is_exclusive(x_397);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_401 = lean_ctor_get(x_397, 1);
x_402 = lean_ctor_get(x_397, 0);
lean_dec(x_402);
x_403 = l_Lean_MessageData_ofList___closed__3;
x_404 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_404, 0, x_391);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_403);
x_406 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_401);
lean_ctor_set(x_397, 1, x_406);
lean_ctor_set(x_397, 0, x_390);
return x_392;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_407 = lean_ctor_get(x_397, 1);
lean_inc(x_407);
lean_dec(x_397);
x_408 = l_Lean_MessageData_ofList___closed__3;
x_409 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_409, 0, x_391);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
x_411 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_407);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_390);
lean_ctor_set(x_412, 1, x_411);
lean_ctor_set(x_392, 0, x_412);
return x_392;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_413 = lean_ctor_get(x_392, 1);
lean_inc(x_413);
lean_dec(x_392);
x_414 = lean_ctor_get(x_397, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_415 = x_397;
} else {
 lean_dec_ref(x_397);
 x_415 = lean_box(0);
}
x_416 = l_Lean_MessageData_ofList___closed__3;
x_417 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_417, 0, x_391);
lean_ctor_set(x_417, 1, x_416);
x_418 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_414);
if (lean_is_scalar(x_415)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_415;
}
lean_ctor_set(x_420, 0, x_390);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_413);
return x_421;
}
}
else
{
uint8_t x_422; 
lean_dec(x_391);
lean_dec(x_390);
x_422 = !lean_is_exclusive(x_392);
if (x_422 == 0)
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_392, 0);
lean_dec(x_423);
return x_392;
}
else
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_392, 1);
lean_inc(x_424);
lean_dec(x_392);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_397);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
}
block_296:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc(x_65);
lean_inc(x_2);
x_66 = l_Array_extract___rarg(x_2, x_54, x_65);
lean_inc(x_2);
x_67 = l_Array_extract___rarg(x_2, x_65, x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
lean_inc(x_67);
x_68 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadIndexDep_x3f(x_67, x_64, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_67);
x_71 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_hasBadParamDep_x3f(x_67, x_62, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_20);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_64);
x_74 = x_64;
x_75 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2(x_67, x_54, x_74);
x_76 = x_75;
x_77 = lean_array_get_size(x_66);
x_78 = lean_nat_sub(x_4, x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_67);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_76);
lean_ctor_set(x_79, 4, x_36);
lean_ctor_set(x_79, 5, x_24);
lean_ctor_set(x_79, 6, x_62);
lean_ctor_set(x_79, 7, x_64);
lean_ctor_set_uint8(x_79, sizeof(void*)*8, x_52);
x_80 = lean_nat_add(x_4, x_58);
lean_dec(x_4);
x_81 = lean_st_ref_get(x_8, x_73);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_get(x_6, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_89 = lean_apply_6(x_3, x_79, x_5, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_88);
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_84, x_5, x_6, x_7, x_8, x_95);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_88, x_5, x_6, x_7, x_8, x_97);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_dec(x_94);
x_102 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_80, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
lean_dec(x_101);
lean_dec(x_100);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_102);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_102, 0);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_107, 1);
x_112 = lean_ctor_get(x_107, 0);
lean_dec(x_112);
x_113 = l_Lean_MessageData_ofList___closed__3;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_101);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_107, 1, x_116);
lean_ctor_set(x_107, 0, x_100);
return x_102;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_107, 1);
lean_inc(x_117);
lean_dec(x_107);
x_118 = l_Lean_MessageData_ofList___closed__3;
x_119 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_119, 0, x_101);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_100);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_102, 0, x_122);
return x_102;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_102, 1);
lean_inc(x_123);
lean_dec(x_102);
x_124 = lean_ctor_get(x_107, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_125 = x_107;
} else {
 lean_dec_ref(x_107);
 x_125 = lean_box(0);
}
x_126 = l_Lean_MessageData_ofList___closed__3;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_101);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_100);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_123);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_101);
lean_dec(x_100);
x_132 = !lean_is_exclusive(x_102);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_102, 0);
lean_dec(x_133);
return x_102;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_102, 1);
lean_inc(x_134);
lean_dec(x_102);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_107);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_98);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_98, 0);
lean_dec(x_137);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 0, x_94);
return x_98;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_98, 1);
lean_inc(x_138);
lean_dec(x_98);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_94);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_24);
x_140 = lean_ctor_get(x_72, 0);
lean_inc(x_140);
lean_dec(x_72);
x_141 = lean_ctor_get(x_71, 1);
lean_inc(x_141);
lean_dec(x_71);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_nat_add(x_4, x_58);
lean_dec(x_4);
lean_inc(x_144);
x_145 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_144);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_148 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__4;
x_150 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_indentExpr(x_20);
x_152 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__6;
x_154 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_indentExpr(x_142);
x_156 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__8;
x_158 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_indentExpr(x_143);
x_160 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_162 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_st_ref_get(x_8, x_141);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_st_ref_get(x_6, x_165);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_162, x_5, x_6, x_7, x_8, x_169);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_166, x_5, x_6, x_7, x_8, x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_170, x_5, x_6, x_7, x_8, x_175);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_dec(x_172);
x_180 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_144, x_5, x_6, x_7, x_8, x_177);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
lean_dec(x_179);
lean_dec(x_178);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
return x_180;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_180);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
else
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_180, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_180);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_180, 0);
lean_dec(x_187);
x_188 = !lean_is_exclusive(x_185);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_189 = lean_ctor_get(x_185, 1);
x_190 = lean_ctor_get(x_185, 0);
lean_dec(x_190);
x_191 = l_Lean_MessageData_ofList___closed__3;
x_192 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_192, 0, x_179);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_189);
lean_ctor_set(x_185, 1, x_194);
lean_ctor_set(x_185, 0, x_178);
return x_180;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_185, 1);
lean_inc(x_195);
lean_dec(x_185);
x_196 = l_Lean_MessageData_ofList___closed__3;
x_197 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_197, 0, x_179);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_178);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_180, 0, x_200);
return x_180;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_180, 1);
lean_inc(x_201);
lean_dec(x_180);
x_202 = lean_ctor_get(x_185, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_203 = x_185;
} else {
 lean_dec_ref(x_185);
 x_203 = lean_box(0);
}
x_204 = l_Lean_MessageData_ofList___closed__3;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_179);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_202);
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_178);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_201);
return x_209;
}
}
else
{
uint8_t x_210; 
lean_dec(x_179);
lean_dec(x_178);
x_210 = !lean_is_exclusive(x_180);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_180, 0);
lean_dec(x_211);
return x_180;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_180, 1);
lean_inc(x_212);
lean_dec(x_180);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_185);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_62);
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
x_214 = !lean_is_exclusive(x_71);
if (x_214 == 0)
{
return x_71;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_71, 0);
x_216 = lean_ctor_get(x_71, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_71);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_36);
lean_dec(x_24);
x_218 = lean_ctor_get(x_69, 0);
lean_inc(x_218);
lean_dec(x_69);
x_219 = lean_ctor_get(x_68, 1);
lean_inc(x_219);
lean_dec(x_68);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_nat_add(x_4, x_58);
lean_dec(x_4);
lean_inc(x_222);
x_223 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_222);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__2;
x_226 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
x_227 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__10;
x_228 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lean_indentExpr(x_20);
x_230 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__12;
x_232 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_indentExpr(x_220);
x_234 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg___closed__14;
x_236 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_indentExpr(x_221);
x_238 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_240 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_st_ref_get(x_8, x_219);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_st_ref_get(x_6, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_240, x_5, x_6, x_7, x_8, x_247);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_244, x_5, x_6, x_7, x_8, x_251);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_248, x_5, x_6, x_7, x_8, x_253);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_ctor_get(x_250, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_250, 1);
lean_inc(x_257);
lean_dec(x_250);
x_258 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___rarg(x_1, x_2, x_3, x_222, x_5, x_6, x_7, x_8, x_255);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
lean_dec(x_257);
lean_dec(x_256);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
return x_258;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_258, 0);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_258);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
else
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_258, 0);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_258);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_258, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_263);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_267 = lean_ctor_get(x_263, 1);
x_268 = lean_ctor_get(x_263, 0);
lean_dec(x_268);
x_269 = l_Lean_MessageData_ofList___closed__3;
x_270 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_270, 0, x_257);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_267);
lean_ctor_set(x_263, 1, x_272);
lean_ctor_set(x_263, 0, x_256);
return x_258;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_263, 1);
lean_inc(x_273);
lean_dec(x_263);
x_274 = l_Lean_MessageData_ofList___closed__3;
x_275 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_275, 0, x_257);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_273);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_256);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_258, 0, x_278);
return x_258;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_279 = lean_ctor_get(x_258, 1);
lean_inc(x_279);
lean_dec(x_258);
x_280 = lean_ctor_get(x_263, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_281 = x_263;
} else {
 lean_dec_ref(x_263);
 x_281 = lean_box(0);
}
x_282 = l_Lean_MessageData_ofList___closed__3;
x_283 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_283, 0, x_257);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
x_285 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_280);
if (lean_is_scalar(x_281)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_281;
}
lean_ctor_set(x_286, 0, x_256);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_279);
return x_287;
}
}
else
{
uint8_t x_288; 
lean_dec(x_257);
lean_dec(x_256);
x_288 = !lean_is_exclusive(x_258);
if (x_288 == 0)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_258, 0);
lean_dec(x_289);
return x_258;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_258, 1);
lean_inc(x_290);
lean_dec(x_258);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_263);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_62);
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
x_292 = !lean_is_exclusive(x_68);
if (x_292 == 0)
{
return x_68;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_68, 0);
x_294 = lean_ctor_get(x_68, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_68);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
}
}
}
else
{
lean_object* x_433; lean_object* x_434; 
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_10);
x_433 = lean_unsigned_to_nat(1u);
x_434 = lean_nat_add(x_4, x_433);
lean_dec(x_4);
x_4 = x_434;
x_9 = x_27;
goto _start;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_10);
x_436 = lean_unsigned_to_nat(1u);
x_437 = lean_nat_add(x_4, x_436);
lean_dec(x_4);
x_4 = x_437;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_439; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_439 = !lean_is_exclusive(x_19);
if (x_439 == 0)
{
return x_19;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_19, 0);
x_441 = lean_ctor_get(x_19, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_19);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
lean_object* x_443; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_443 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg(x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_443;
}
}
else
{
uint8_t x_444; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_14);
if (x_444 == 0)
{
return x_14;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_14, 0);
x_446 = lean_ctor_get(x_14, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_14);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
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
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Init_Data_Array_Basic_8__allDiffAuxAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_Basic_9__allDiffAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__4(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConstOf(x_2, x_1);
return x_3;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = 8192;
x_5 = l_Lean_Expr_FindImpl_initCache;
x_6 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_3, x_4, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 1;
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(x_1, x_2);
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
x_14 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_2);
lean_inc(x_1);
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
x_7 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_912____spec__1___rarg(x_6, x_1, x_2, x_3, x_4, x_5);
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_1, x_1, x_9, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1(x_3, x_4, x_21, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_14);
x_16 = l_Array_extract___rarg(x_1, x_15, x_13);
x_17 = l_Lean_Expr_replaceFVars(x_3, x_2, x_16);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_18);
lean_dec(x_18);
x_21 = lean_expr_eqv(x_20, x_6);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__2(x_19, x_4, x_16, x_5, x_27, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwToBelowFailed___rarg(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_29;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
lean_inc(x_1);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = lean_array_get_size(x_4);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_le(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_2);
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
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__3(x_17, x_4, x_5, x_1, x_2, x_3, x_26, x_6, x_7, x_8, x_9, x_10);
return x_27;
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
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_662____closed__2;
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
x_10 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_2, x_5, x_6, x_7, x_8, x_9);
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
x_147 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_146, x_5, x_6, x_7, x_8, x_145);
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
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed), 10, 3);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_4);
lean_closure_set(x_25, 2, x_1);
x_26 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_11, x_25, x_5, x_6, x_7, x_8, x_13);
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
x_38 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_37, x_28, x_5, x_6, x_7, x_8, x_35);
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
x_45 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_36, x_5, x_6, x_7, x_8, x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_48 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_47, x_28, x_5, x_6, x_7, x_8, x_46);
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
x_59 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_36, x_5, x_6, x_7, x_8, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__5;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_61, x_28, x_5, x_6, x_7, x_8, x_60);
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
x_81 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_80, x_71, x_5, x_6, x_7, x_8, x_78);
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
x_88 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_79, x_5, x_6, x_7, x_8, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_91 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_90, x_71, x_5, x_6, x_7, x_8, x_89);
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
x_102 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_79, x_5, x_6, x_7, x_8, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__10;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_105 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_104, x_71, x_5, x_6, x_7, x_8, x_103);
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
x_113 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed), 10, 3);
lean_closure_set(x_113, 0, x_3);
lean_closure_set(x_113, 1, x_4);
lean_closure_set(x_113, 2, x_1);
x_114 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_11, x_113, x_5, x_6, x_7, x_8, x_13);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_16);
lean_dec(x_14);
x_115 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed), 10, 3);
lean_closure_set(x_115, 0, x_3);
lean_closure_set(x_115, 1, x_4);
lean_closure_set(x_115, 2, x_1);
x_116 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_11, x_115, x_5, x_6, x_7, x_8, x_13);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_15);
lean_dec(x_14);
x_117 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed), 10, 3);
lean_closure_set(x_117, 0, x_3);
lean_closure_set(x_117, 1, x_4);
lean_closure_set(x_117, 2, x_1);
x_118 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_11, x_117, x_5, x_6, x_7, x_8, x_13);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_14);
x_119 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed), 10, 3);
lean_closure_set(x_119, 0, x_3);
lean_closure_set(x_119, 1, x_4);
lean_closure_set(x_119, 2, x_1);
x_120 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_11, x_119, x_5, x_6, x_7, x_8, x_13);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed), 10, 3);
lean_closure_set(x_121, 0, x_3);
lean_closure_set(x_121, 1, x_4);
lean_closure_set(x_121, 2, x_1);
x_122 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_11, x_121, x_5, x_6, x_7, x_8, x_13);
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
x_133 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_134 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_136 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_135, x_134, x_5, x_6, x_7, x_8, x_125);
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_5);
x_11 = l_Lean_mkApp(x_1, x_5);
x_12 = lean_array_get_size(x_2);
x_13 = l_Array_extract___rarg(x_2, x_3, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_13, x_13, x_14, x_11);
lean_dec(x_13);
x_16 = lean_apply_7(x_4, x_5, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("C");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Expr_Lean_Expr___instance__11;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get(x_12, x_5, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__2;
x_19 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_18, x_9, x_10, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__1), 10, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_4);
x_23 = 0;
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1___rarg(x_20, x_23, x_16, x_22, x_7, x_8, x_9, x_10, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_13 = l_Array_extract___rarg(x_1, x_12, x_2);
x_14 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_13, x_13, x_12, x_3);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_15 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___boxed), 11, 4);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
x_19 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
x_20 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_16, x_19, x_18, x_7, x_8, x_9, x_10, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected 'below' type");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_indentExpr(x_3);
x_23 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_26, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__3(x_5, x_1, x_4, x_19, x_2, x_32, x_7, x_8, x_9, x_10, x_11);
return x_33;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg), 11, 0);
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
x_9 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
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
x_40 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_39, x_4, x_5, x_6, x_7, x_38);
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
x_14 = l_Lean_Expr_getAppNumArgsAux(x_10, x_13);
x_15 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_10);
x_19 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg(x_2, x_3, x_10, x_10, x_16, x_18, x_4, x_5, x_6, x_7, x_12);
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
x_26 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_29 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_28, x_27, x_4, x_5, x_6, x_7, x_22);
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
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
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
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_nat_dec_le(x_15, x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_7, x_19);
lean_dec(x_7);
x_21 = lean_nat_dec_eq(x_4, x_8);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
x_23 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_22, x_8);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Expr_Lean_Expr___instance__11;
x_25 = lean_array_get(x_24, x_5, x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_25, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_push(x_9, x_27);
x_30 = lean_ctor_get(x_6, 2);
x_31 = lean_nat_add(x_8, x_30);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_31;
x_9 = x_29;
x_14 = x_28;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
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
x_37 = lean_ctor_get(x_6, 2);
x_38 = lean_nat_add(x_8, x_37);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_38;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_6, 2);
x_41 = lean_nat_add(x_8, x_40);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_14);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_14);
return x_44;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_array_get_size(x_1);
x_14 = l_Array_extract___rarg(x_1, x_2, x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_3, x_4, x_5, x_6, x_14, x_18, x_15, x_16, x_19, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_16, x_7);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_24, x_24, x_16, x_7);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to eliminate recursive application");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_Expr_Lean_Expr___instance__11;
x_16 = lean_array_get(x_15, x_1, x_2);
x_17 = lean_ctor_get(x_5, 6);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_6, x_18, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__1(x_1, x_3, x_4, x_5, x_6, x_7, x_20, x_10, x_11, x_12, x_13, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_indentExpr(x_8);
x_25 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_28, x_10, x_11, x_12, x_13, x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("insufficient number of parameters at recursive application ");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
x_19 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = x_6;
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__1), 10, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_23);
x_26 = x_25;
x_27 = lean_apply_5(x_26, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_29, x_29, x_24, x_21);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_31, x_31, x_24, x_21);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_5);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
x_46 = lean_nat_add(x_44, x_45);
x_47 = lean_array_get_size(x_6);
x_48 = lean_nat_dec_le(x_47, x_46);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2(x_6, x_46, x_44, x_1, x_2, x_3, x_45, x_4, x_49, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_45);
lean_dec(x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_indentExpr(x_4);
x_52 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_55, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_nat_dec_le(x_15, x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_7, x_19);
lean_dec(x_7);
x_21 = lean_nat_dec_eq(x_4, x_8);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
x_23 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_22, x_8);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Expr_Lean_Expr___instance__11;
x_25 = lean_array_get(x_24, x_5, x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_25, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_push(x_9, x_27);
x_30 = lean_ctor_get(x_6, 2);
x_31 = lean_nat_add(x_8, x_30);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_31;
x_9 = x_29;
x_14 = x_28;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
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
x_37 = lean_ctor_get(x_6, 2);
x_38 = lean_nat_add(x_8, x_37);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_38;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_6, 2);
x_41 = lean_nat_add(x_8, x_40);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_14);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_14);
return x_44;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_array_get_size(x_1);
x_14 = l_Array_extract___rarg(x_1, x_2, x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_3, x_4, x_5, x_6, x_14, x_18, x_15, x_16, x_19, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_16, x_7);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_24, x_24, x_16, x_7);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_Expr_Lean_Expr___instance__11;
x_16 = lean_array_get(x_15, x_1, x_2);
x_17 = lean_ctor_get(x_5, 6);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_6, x_18, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__1(x_1, x_3, x_4, x_5, x_6, x_7, x_20, x_10, x_11, x_12, x_13, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_indentExpr(x_8);
x_25 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_28, x_10, x_11, x_12, x_13, x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
x_19 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = x_6;
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__4), 10, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_23);
x_26 = x_25;
x_27 = lean_apply_5(x_26, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_29, x_29, x_24, x_21);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_31, x_31, x_24, x_21);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_5);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
x_46 = lean_nat_add(x_44, x_45);
x_47 = lean_array_get_size(x_6);
x_48 = lean_nat_dec_le(x_47, x_46);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__2(x_6, x_46, x_44, x_1, x_2, x_3, x_45, x_4, x_49, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_45);
lean_dec(x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_indentExpr(x_4);
x_52 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_55, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_nat_dec_le(x_15, x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_7, x_19);
lean_dec(x_7);
x_21 = lean_nat_dec_eq(x_4, x_8);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
x_23 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_22, x_8);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Expr_Lean_Expr___instance__11;
x_25 = lean_array_get(x_24, x_5, x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_25, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_push(x_9, x_27);
x_30 = lean_ctor_get(x_6, 2);
x_31 = lean_nat_add(x_8, x_30);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_31;
x_9 = x_29;
x_14 = x_28;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
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
x_37 = lean_ctor_get(x_6, 2);
x_38 = lean_nat_add(x_8, x_37);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_38;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_6, 2);
x_41 = lean_nat_add(x_8, x_40);
lean_dec(x_8);
x_7 = x_20;
x_8 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_14);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_14);
return x_44;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_array_get_size(x_1);
x_14 = l_Array_extract___rarg(x_1, x_2, x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8(x_3, x_4, x_5, x_6, x_14, x_18, x_15, x_16, x_19, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_16, x_7);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_24, x_24, x_16, x_7);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_Expr_Lean_Expr___instance__11;
x_16 = lean_array_get(x_15, x_1, x_2);
x_17 = lean_ctor_get(x_5, 6);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelow(x_6, x_18, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__1(x_1, x_3, x_4, x_5, x_6, x_7, x_20, x_10, x_11, x_12, x_13, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_indentExpr(x_8);
x_25 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_28, x_10, x_11, x_12, x_13, x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
x_19 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = x_6;
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__7), 10, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_23);
x_26 = x_25;
x_27 = lean_apply_5(x_26, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_29, x_29, x_24, x_21);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_31, x_31, x_24, x_21);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_5);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
x_46 = lean_nat_add(x_44, x_45);
x_47 = lean_array_get_size(x_6);
x_48 = lean_nat_dec_le(x_47, x_46);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__2(x_6, x_46, x_44, x_1, x_2, x_3, x_45, x_4, x_49, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_45);
lean_dec(x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_indentExpr(x_4);
x_52 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_55, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_1, x_12);
x_14 = l_Lean_Expr_Lean_Expr___instance__11;
x_15 = lean_array_get(x_14, x_2, x_13);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_3, x_4, x_15, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_2, x_17, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected matcher application alternative");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nat application");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("altNumParams: ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", xs: ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_33; lean_object* x_34; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_get(x_11, x_12);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = 0;
x_33 = x_56;
x_34 = x_55;
goto block_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_59 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_58, x_8, x_9, x_10, x_11, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unbox(x_60);
lean_dec(x_60);
x_33 = x_62;
x_34 = x_61;
goto block_50;
}
block_32:
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_indentExpr(x_4);
x_17 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_5);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_24, x_8, x_9, x_10, x_11, x_13);
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
lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__1(x_1, x_6, x_2, x_3, x_7, x_30, x_8, x_9, x_10, x_11, x_13);
lean_dec(x_1);
return x_31;
}
}
block_50:
{
if (x_33 == 0)
{
x_13 = x_34;
goto block_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_1);
x_35 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_1);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__6;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__8;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Array_toList___rarg(x_6);
x_42 = l_List_map___main___at_Lean_MessageData_Lean_Message___instance__12___spec__1(x_41);
x_43 = l_Lean_MessageData_ofList(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_48 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_47, x_46, x_8, x_9, x_10, x_11, x_34);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_13 = x_49;
goto block_32;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_3);
lean_inc(x_19);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2), 12, 5);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10___rarg(x_19, x_21, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_17 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_16, x_13, x_6, x_7, x_8, x_9, x_14);
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
x_17 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(x_16, x_13, x_6, x_7, x_8, x_9, x_14);
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
x_14 = l_Lean_Expr_getAppNumArgsAux(x_4, x_13);
x_15 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_4);
x_19 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3(x_1, x_2, x_3, x_4, x_4, x_16, x_18, x_5, x_6, x_7, x_8, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_1);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_containsRecFn(x_1, x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux(x_4, x_23);
x_25 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_24, x_27);
lean_dec(x_24);
lean_inc(x_4);
x_29 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6(x_1, x_2, x_3, x_4, x_4, x_26, x_28, x_5, x_6, x_7, x_8, x_20);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Expr_getAppNumArgsAux(x_4, x_30);
x_32 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
lean_inc(x_3);
x_36 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg), 7, 2);
lean_closure_set(x_36, 0, x_21);
lean_closure_set(x_36, 1, x_3);
x_37 = lean_st_ref_get(x_8, x_20);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_6, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_n(x_4, 2);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9(x_1, x_2, x_3, x_4, x_4, x_33, x_35, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_40, x_5, x_6, x_7, x_8, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_44, x_5, x_6, x_7, x_8, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l_Lean_Meta_mapErrorImp___rarg(x_36, x_51, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 1);
x_58 = lean_ctor_get(x_53, 2);
x_59 = lean_ctor_get(x_53, 3);
x_60 = lean_ctor_get(x_53, 4);
x_61 = lean_ctor_get(x_53, 5);
x_62 = lean_ctor_get(x_53, 6);
x_63 = lean_ctor_get(x_53, 7);
x_64 = lean_ctor_get(x_53, 8);
x_65 = l_Array_zip___rarg(x_63, x_62);
lean_dec(x_63);
x_66 = x_65;
x_67 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11), 10, 5);
lean_closure_set(x_67, 0, x_1);
lean_closure_set(x_67, 1, x_2);
lean_closure_set(x_67, 2, x_4);
lean_closure_set(x_67, 3, x_30);
lean_closure_set(x_67, 4, x_66);
x_68 = x_67;
x_69 = lean_apply_5(x_68, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_ctor_set(x_53, 7, x_71);
x_72 = l_Lean_Meta_MatcherApp_toExpr(x_53);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
lean_ctor_set(x_53, 7, x_73);
x_75 = l_Lean_Meta_MatcherApp_toExpr(x_53);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_free_object(x_53);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_81 = lean_ctor_get(x_53, 0);
x_82 = lean_ctor_get(x_53, 1);
x_83 = lean_ctor_get(x_53, 2);
x_84 = lean_ctor_get(x_53, 3);
x_85 = lean_ctor_get(x_53, 4);
x_86 = lean_ctor_get(x_53, 5);
x_87 = lean_ctor_get(x_53, 6);
x_88 = lean_ctor_get(x_53, 7);
x_89 = lean_ctor_get(x_53, 8);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_53);
x_90 = l_Array_zip___rarg(x_88, x_87);
lean_dec(x_88);
x_91 = x_90;
x_92 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11), 10, 5);
lean_closure_set(x_92, 0, x_1);
lean_closure_set(x_92, 1, x_2);
lean_closure_set(x_92, 2, x_4);
lean_closure_set(x_92, 3, x_30);
lean_closure_set(x_92, 4, x_91);
x_93 = x_92;
x_94 = lean_apply_5(x_93, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_82);
lean_ctor_set(x_98, 2, x_83);
lean_ctor_set(x_98, 3, x_84);
lean_ctor_set(x_98, 4, x_85);
lean_ctor_set(x_98, 5, x_86);
lean_ctor_set(x_98, 6, x_87);
lean_ctor_set(x_98, 7, x_95);
lean_ctor_set(x_98, 8, x_89);
x_99 = l_Lean_Meta_MatcherApp_toExpr(x_98);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_103 = x_94;
} else {
 lean_dec_ref(x_94);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_52);
if (x_105 == 0)
{
return x_52;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_52, 0);
x_107 = lean_ctor_get(x_52, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_52);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
case 6:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint64_t x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_4, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_4, 2);
lean_inc(x_111);
x_112 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_113 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_110, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = (uint8_t)((x_112 << 24) >> 61);
x_117 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2___boxed), 10, 4);
lean_closure_set(x_117, 0, x_111);
lean_closure_set(x_117, 1, x_1);
lean_closure_set(x_117, 2, x_2);
lean_closure_set(x_117, 3, x_3);
x_118 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1___rarg(x_109, x_116, x_114, x_117, x_5, x_6, x_7, x_8, x_115);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_113);
if (x_119 == 0)
{
return x_113;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_113, 0);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_113);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
case 7:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint64_t x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_4, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_4, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_4, 2);
lean_inc(x_125);
x_126 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_127 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_124, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = (uint8_t)((x_126 << 24) >> 61);
x_131 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__3___boxed), 10, 4);
lean_closure_set(x_131, 0, x_125);
lean_closure_set(x_131, 1, x_1);
lean_closure_set(x_131, 2, x_2);
lean_closure_set(x_131, 3, x_3);
x_132 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__1___rarg(x_123, x_130, x_128, x_131, x_5, x_6, x_7, x_8, x_129);
return x_132;
}
else
{
uint8_t x_133; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_127);
if (x_133 == 0)
{
return x_127;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_127, 0);
x_135 = lean_ctor_get(x_127, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_127);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_4, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_4, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_4, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_4, 3);
lean_inc(x_140);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_141 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_138, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_144 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_139, x_5, x_6, x_7, x_8, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__2___boxed), 10, 4);
lean_closure_set(x_147, 0, x_140);
lean_closure_set(x_147, 1, x_1);
lean_closure_set(x_147, 2, x_2);
lean_closure_set(x_147, 3, x_3);
x_148 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__12___rarg(x_137, x_142, x_145, x_147, x_5, x_6, x_7, x_8, x_146);
return x_148;
}
else
{
uint8_t x_149; 
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_137);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_144);
if (x_149 == 0)
{
return x_144;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_144, 0);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_144);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_141);
if (x_153 == 0)
{
return x_141;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_141, 0);
x_155 = lean_ctor_get(x_141, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_141);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
case 10:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_4, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_4, 1);
lean_inc(x_158);
lean_dec(x_4);
x_159 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_158, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = l_Lean_mkMData(x_157, x_161);
lean_ctor_set(x_159, 0, x_162);
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_159, 0);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_159);
x_165 = l_Lean_mkMData(x_157, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
uint8_t x_167; 
lean_dec(x_157);
x_167 = !lean_is_exclusive(x_159);
if (x_167 == 0)
{
return x_159;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_159, 0);
x_169 = lean_ctor_get(x_159, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_159);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
case 11:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_4, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_4, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_4, 2);
lean_inc(x_173);
lean_dec(x_4);
x_174 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop(x_1, x_2, x_3, x_173, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = l_Lean_mkProj(x_171, x_172, x_176);
lean_ctor_set(x_174, 0, x_177);
return x_174;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_174, 0);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_174);
x_180 = l_Lean_mkProj(x_171, x_172, x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
uint8_t x_182; 
lean_dec(x_172);
lean_dec(x_171);
x_182 = !lean_is_exclusive(x_174);
if (x_182 == 0)
{
return x_174;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_174, 0);
x_184 = lean_ctor_get(x_174, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_174);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
default: 
{
lean_object* x_186; 
lean_dec(x_3);
lean_dec(x_2);
x_186 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_ensureNoRecFn(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_186;
}
}
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
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__9___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
lean_inc(x_10);
x_18 = l_Array_extract___rarg(x_10, x_17, x_1);
x_19 = l_Lean_Expr_Lean_Expr___instance__11;
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
x_32 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_30, x_12, x_13, x_14, x_15, x_31);
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
x_15 = l_Lean_Expr_Lean_Expr___instance__11;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_8, x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_17, x_10, x_11, x_12, x_13, x_14);
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
x_29 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_19, x_27, x_28, x_10, x_11, x_12, x_13, x_20);
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOnType ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn     ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn motive: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 7);
lean_inc(x_16);
lean_inc(x_2);
lean_inc(x_16);
x_17 = lean_array_push(x_16, x_2);
lean_inc(x_11);
x_18 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_17, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_105; lean_object* x_106; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_115 = lean_st_ref_get(x_14, x_20);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = 0;
x_105 = x_120;
x_106 = x_119;
goto block_114;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_dec(x_115);
lean_inc(x_7);
x_122 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_7, x_11, x_12, x_13, x_14, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_unbox(x_123);
lean_dec(x_123);
x_105 = x_125;
x_106 = x_124;
goto block_114;
}
block_104:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 6);
lean_inc(x_22);
if (x_8 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_1, 4);
lean_inc(x_93);
x_94 = l_Lean_Meta_brecOnSuffix;
x_95 = lean_name_mk_string(x_93, x_94);
x_96 = lean_ctor_get(x_1, 5);
lean_inc(x_96);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_9);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_mkConst(x_95, x_97);
x_23 = x_98;
goto block_92;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_9);
x_99 = lean_ctor_get(x_1, 4);
lean_inc(x_99);
x_100 = l_Lean_Meta_binductionOnSuffix;
x_101 = lean_name_mk_string(x_99, x_100);
x_102 = lean_ctor_get(x_1, 5);
lean_inc(x_102);
x_103 = l_Lean_mkConst(x_101, x_102);
x_23 = x_103;
goto block_92;
}
block_92:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_24, x_23);
lean_dec(x_22);
x_26 = l_Lean_mkApp(x_25, x_19);
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_16, x_16, x_24, x_26);
lean_inc(x_2);
x_28 = l_Lean_mkApp(x_27, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_28);
x_29 = l_Lean_Meta_check(x_28, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_28);
x_31 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_28, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_50; uint8_t x_63; lean_object* x_64; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_73 = lean_st_ref_get(x_14, x_33);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = 0;
x_63 = x_78;
x_64 = x_77;
goto block_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
lean_inc(x_7);
x_80 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_7, x_11, x_12, x_13, x_14, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_63 = x_83;
x_64 = x_82;
goto block_72;
}
block_49:
{
if (x_34 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed), 14, 7);
lean_closure_set(x_36, 0, x_16);
lean_closure_set(x_36, 1, x_4);
lean_closure_set(x_36, 2, x_5);
lean_closure_set(x_36, 3, x_2);
lean_closure_set(x_36, 4, x_6);
lean_closure_set(x_36, 5, x_1);
lean_closure_set(x_36, 6, x_28);
x_37 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
x_38 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_32, x_37, x_36, x_11, x_12, x_13, x_14, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_32);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_32);
x_40 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__2;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_7, x_43, x_11, x_12, x_13, x_14, x_35);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__2___boxed), 14, 7);
lean_closure_set(x_46, 0, x_16);
lean_closure_set(x_46, 1, x_4);
lean_closure_set(x_46, 2, x_5);
lean_closure_set(x_46, 3, x_2);
lean_closure_set(x_46, 4, x_6);
lean_closure_set(x_46, 5, x_1);
lean_closure_set(x_46, 6, x_28);
x_47 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
x_48 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_32, x_47, x_46, x_11, x_12, x_13, x_14, x_45);
return x_48;
}
}
block_62:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_get(x_14, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = 0;
x_34 = x_56;
x_35 = x_55;
goto block_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
lean_inc(x_7);
x_58 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_7, x_11, x_12, x_13, x_14, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_34 = x_61;
x_35 = x_60;
goto block_49;
}
}
block_72:
{
if (x_63 == 0)
{
x_50 = x_64;
goto block_62;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_28);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_28);
x_66 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__4;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_7);
x_70 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_7, x_69, x_11, x_12, x_13, x_14, x_64);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_50 = x_71;
goto block_62;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_28);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_31);
if (x_84 == 0)
{
return x_31;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_31, 0);
x_86 = lean_ctor_get(x_31, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_31);
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
lean_dec(x_28);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_29);
if (x_88 == 0)
{
return x_29;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_29, 0);
x_90 = lean_ctor_get(x_29, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_29);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
block_114:
{
if (x_105 == 0)
{
x_21 = x_106;
goto block_104;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_19);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_19);
x_108 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__6;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_7);
x_112 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_7, x_111, x_11, x_12, x_13, x_14, x_106);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_21 = x_113;
goto block_104;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_18);
if (x_126 == 0)
{
return x_18;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_18, 0);
x_128 = lean_ctor_get(x_18, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_18);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn univ: ");
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_3, x_4, x_5, x_6, x_7, x_8);
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
x_15 = l_Lean_Expr_Lean_Expr___instance__11;
x_16 = lean_array_get(x_15, x_13, x_14);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_filterAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___spec__1(x_2, x_16, x_13, x_17, x_17);
lean_inc(x_4);
lean_inc(x_18);
x_19 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(x_18, x_12, x_4, x_5, x_6, x_7, x_11);
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
x_22 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_20, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_51; lean_object* x_52; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_62 = lean_st_ref_get(x_7, x_24);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = 0;
x_51 = x_67;
x_52 = x_66;
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_70 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_69, x_4, x_5, x_6, x_7, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
x_51 = x_73;
x_52 = x_72;
goto block_61;
}
block_50:
{
uint8_t x_26; uint8_t x_27; 
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
if (x_26 == 0)
{
uint8_t x_47; 
x_47 = 0;
x_27 = x_47;
goto block_46;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_levelZero;
x_49 = lean_level_eq(x_23, x_48);
x_27 = x_49;
goto block_46;
}
block_46:
{
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_29 = lean_box(0);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3(x_2, x_16, x_20, x_18, x_3, x_1, x_28, x_27, x_23, x_29, x_4, x_5, x_6, x_7, x_25);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_levelZero;
x_32 = lean_level_eq(x_23, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Meta_decLevel___at_Lean_Meta_getDecLevel___spec__1(x_23, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_37 = lean_box(0);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3(x_2, x_16, x_20, x_18, x_3, x_1, x_36, x_27, x_34, x_37, x_4, x_5, x_6, x_7, x_35);
return x_38;
}
else
{
uint8_t x_39; 
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
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_44 = lean_box(0);
x_45 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3(x_2, x_16, x_20, x_18, x_3, x_1, x_43, x_27, x_23, x_44, x_4, x_5, x_6, x_7, x_25);
return x_45;
}
}
}
}
block_61:
{
if (x_51 == 0)
{
x_25 = x_52;
goto block_50;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_23);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_23);
x_54 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_toBelowAux___closed__12;
x_59 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_58, x_57, x_4, x_5, x_6, x_7, x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_25 = x_60;
goto block_50;
}
}
}
else
{
uint8_t x_74; 
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
x_74 = !lean_is_exclusive(x_22);
if (x_74 == 0)
{
return x_22;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_22, 0);
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_22);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_19);
if (x_78 == 0)
{
return x_19;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_19, 0);
x_80 = lean_ctor_get(x_19, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_9);
if (x_82 == 0)
{
return x_9;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_9, 0);
x_84 = lean_ctor_get(x_9, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_9);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
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
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_17;
}
}
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
x_12 = lean_st_ref_set(x_5, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_st_ref_set(x_5, x_22, x_9);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
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
x_15 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_3, x_13, x_7, x_8, x_9, x_10, x_14);
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
x_75 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_5, x_7, x_8, x_9, x_10, x_74);
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
x_43 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_5, x_44, x_7, x_8, x_9, x_10, x_19);
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
lean_object* x_1; 
x_1 = lean_mk_string(" :=\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1;
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
x_47 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_46, x_4, x_5, x_6, x_7, x_45);
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
x_22 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_processAssignmentFOApprox_loop___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_toList___rarg(x_2);
x_27 = l_List_map___main___at_Lean_MessageData_Lean_Message___instance__12___spec__1(x_26);
x_28 = l_Lean_MessageData_ofList(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2;
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
x_36 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_35, x_34, x_4, x_5, x_6, x_7, x_19);
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
x_13 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__10___rarg(x_7, x_8, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___spec__1(x_12, x_2, x_3, x_4, x_5, x_15);
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
x_23 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___spec__1(x_12, x_2, x_3, x_4, x_5, x_22);
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
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l_Lean_Elab_structuralRecursion___closed__3;
x_13 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Elab_PreDefinition_inhabited;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion(x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_21 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_18, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_addAndCompileUnsafeRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
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
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
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
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_3445_(lean_object* x_1) {
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
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_throwStructuralFailed___rarg___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_findRecArg_loop___spec__2___closed__3);
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
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___spec__1___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_withBelowDict___rarg___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__3___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__4 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__4);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__5 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__5);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__6 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__6);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__7 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__7();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__7);
l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__8 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__8();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___spec__11___lambda__2___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_replaceRecApps_loop___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___lambda__3___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_mkBRecOn___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_elimRecursion___lambda__2___closed__2);
l_Lean_Elab_structuralRecursion___closed__1 = _init_l_Lean_Elab_structuralRecursion___closed__1();
lean_mark_persistent(l_Lean_Elab_structuralRecursion___closed__1);
l_Lean_Elab_structuralRecursion___closed__2 = _init_l_Lean_Elab_structuralRecursion___closed__2();
lean_mark_persistent(l_Lean_Elab_structuralRecursion___closed__2);
l_Lean_Elab_structuralRecursion___closed__3 = _init_l_Lean_Elab_structuralRecursion___closed__3();
lean_mark_persistent(l_Lean_Elab_structuralRecursion___closed__3);
res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_3445_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
