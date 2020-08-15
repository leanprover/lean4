// Lean compiler output
// Module: Lean.Meta.EqnCompiler.DepElim
// Imports: Init Lean.Util.CollectLevelParams Lean.Meta.Check Lean.Meta.Tactic.Cases Lean.Meta.GeneralizeTelescope Lean.Meta.EqnCompiler.MVarRenaming Lean.Meta.EqnCompiler.CaseValues Lean.Meta.EqnCompiler.CaseArraySizes
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
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__51;
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__2___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_unify___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6(lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_unify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__2;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__1;
lean_object* l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_applyFVarSubst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_toMessageData___main___closed__2;
lean_object* l_Lean_Meta_DepElim_counterExampleToMessageData(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main(lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_toMessageData___main___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_Nat_foldAux___main___at_Lean_Meta_DepElim_mkElim___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_DepElim_mkElim___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__4;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__1;
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__6;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_isAltVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__4;
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__8;
lean_object* l_Lean_Meta_DepElim_replaceFVarIdAtLocalDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkThunkType(lean_object*);
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__2;
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___closed__1;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__1;
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__6;
lean_object* l_Lean_Meta_withExistingLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2;
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__8;
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___boxed(lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__1;
lean_object* l_Lean_Meta_DepElim_examplesToMessageData(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
lean_object* l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l_Lean_Meta_DepElim_Unify_assign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__1;
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_unify___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_isAltVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__3;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getEnv___boxed(lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_4__isDone(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_mkElim___spec__1(lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_DepElim_Pattern_toExpr___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_withGoalOf___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__3;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__4___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___spec__1(uint8_t, lean_object*);
lean_object* l_Std_HashSetImp_contains___at_Lean_Meta_DepElim_mkElim___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___boxed(lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
extern lean_object* l_Lean_unitToExpr___lambda__1___closed__3;
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern(lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__4;
lean_object* l_Lean_Meta_DepElim_Unify_unify___main___closed__1;
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_unify___main___closed__3;
lean_object* l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_toMessageData___closed__3;
lean_object* l_Lean_Meta_caseValueAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__6;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__9;
lean_object* l_Std_HashSetImp_insert___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__3;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__7(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__2(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__1;
uint8_t l_List_elem___main___at_Lean_Occurrences_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_Inhabited;
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__3(lean_object*);
lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___boxed(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_5__isNextVar___boxed(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElimTester(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__3;
lean_object* l_Lean_Meta_throwOther___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(lean_object*, lean_object*);
lean_object* l_Std_HashSetImp_expand___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__2(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___spec__1(uint8_t, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_27__isFirstPatternVar(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__2(lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_Inhabited___closed__1;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__5;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___boxed(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__11;
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst___main(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__7;
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayHasFormat___rarg___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___closed__1;
lean_object* l_Std_HashSetImp_moveEntries___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLocalDeclMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__3;
lean_object* l_Lean_Meta_DepElim_Problem_Inhabited___closed__1;
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_23__unify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__2;
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tracer___closed__3;
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__2___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_toMessageData___main___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern(lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___closed__2;
lean_object* l_Lean_Meta_DepElim_Unify_occurs___boxed(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
lean_object* l_Lean_Meta_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_assignGoalOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Meta_FVarSubst_find_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__4;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_Lean_Meta_DepElim_Example_varsToUnderscore(lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__12;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__1;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__5;
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___spec__1(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___boxed(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__2;
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__2(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__1;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition(lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_unify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___spec__1(uint8_t, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__3;
lean_object* l_Lean_Meta_DepElim_Unify_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_DepElim_Problem_Inhabited;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___boxed(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__5;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable___spec__1(lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ctorName(lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSet___at_Lean_Meta_DepElim_mkElim___spec__2(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__8;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__1;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1(lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition(lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__2;
uint8_t l_Lean_Meta_DepElim_Unify_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Meta_DepElim_mkElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_counterExamplesToMessageData(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern(lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___boxed(lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__6;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__6;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_withGoalOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_counterExamplesToMessageData___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__3;
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData(lean_object*);
lean_object* l_Lean_Meta_DepElim_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_23__unify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_toMessageData___closed__4;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___spec__1(uint8_t, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_toMessageData___closed__2;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__10;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_4__isDone___boxed(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__1;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__7;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_expandIfVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__5;
lean_object* l_Lean_Meta_admit(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__3;
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElimTester___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__1(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_varsToUnderscore___main(lean_object*);
extern lean_object* l_Lean_Meta_evalNat___main___closed__17;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_examplesToMessageData___spec__1(lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___spec__1(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_toMessageData___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__3;
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_unify___main___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__3;
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___spec__1(uint8_t, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable(lean_object*);
lean_object* l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__4;
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___boxed(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_39__mkElimSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__1(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Position_lt___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_27__isFirstPatternVar___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_Inhabited;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__2;
lean_object* l_Lean_Meta_DepElim_Unify_expandIfVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__1;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_assignGoalOf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_21__throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__1;
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__2___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__2;
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___spec__1(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__7;
extern lean_object* l_Lean_Meta_evalNat___main___closed__1;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_toMessageData___main(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___boxed(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_39__mkElimSort(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__1;
uint8_t l_Std_AssocList_contains___main___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__5;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__7;
lean_object* l_Lean_Meta_DepElim_withGoalOf(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__2(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Alt_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___boxed(lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues(lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___boxed(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___closed__5;
lean_object* l_Lean_Meta_DepElim_Alt_Inhabited___closed__1;
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__5;
lean_object* l_Lean_Meta_DepElim_mkElimTester___closed__2;
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes(lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElimTester___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_beqOfEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__3;
lean_object* l_Nat_foldAux___main___at_Lean_Meta_DepElim_mkElim___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__regTraceClasses___closed__2;
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__1(lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___spec__1(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_DepElim_mkElimTester___closed__1;
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__1;
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_21__throwInductiveTypeExpected(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__2(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited___closed__1;
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern(lean_object*);
lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux(lean_object*);
lean_object* l_Lean_Meta_DepElim_Unify_assign___closed__6;
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_40__regTraceClasses(lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___spec__1(uint8_t, uint8_t, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Pattern_toExpr___main(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__3;
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_5__isNextVar(lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__2;
lean_object* l_Lean_Meta_generalizeTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_Example_toMessageData(lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DepElim_replaceFVarIdAtLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_LocalDecl_fvarId(x_3);
x_5 = lean_name_eq(x_4, x_1);
lean_dec(x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 3);
x_8 = l_Lean_Expr_replaceFVarId(x_7, x_1, x_2);
lean_dec(x_7);
lean_ctor_set(x_3, 3, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = l_Lean_Expr_replaceFVarId(x_12, x_1, x_2);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
lean_inc(x_1);
x_19 = l_Lean_Expr_replaceFVarId(x_17, x_1, x_2);
lean_dec(x_17);
x_20 = l_Lean_Expr_replaceFVarId(x_18, x_1, x_2);
lean_dec(x_18);
lean_ctor_set(x_3, 4, x_20);
lean_ctor_set(x_3, 3, x_19);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_1);
x_26 = l_Lean_Expr_replaceFVarId(x_24, x_1, x_2);
lean_dec(x_24);
x_27 = l_Lean_Expr_replaceFVarId(x_25, x_1, x_2);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
return x_28;
}
}
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Meta_DepElim_replaceFVarIdAtLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DepElim_replaceFVarIdAtLocalDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_Inhabited___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DepElim_Pattern_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_List_foldl___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_3);
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_4);
x_7 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_8);
x_11 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".(");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_paren___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_paren___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__3;
x_5 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_mkFVar(x_8);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__5;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_MessageData_Inhabited___closed__1;
x_19 = l_List_foldl___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__1(x_18, x_11);
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
case 3:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_toMessageData___main___spec__2(x_25);
x_27 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_28 = l_Lean_MessageData_joinSep___main(x_26, x_27);
lean_dec(x_26);
x_29 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lean_mkFVar(x_33);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__8;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_34);
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_DepElim_Pattern_toExpr___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_9 = l_Lean_Meta_DepElim_Pattern_toExpr___main(x_7, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Meta_DepElim_Pattern_toExpr___main___spec__1(x_8, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_free_object(x_1);
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
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_2);
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
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_2);
x_28 = l_Lean_Meta_DepElim_Pattern_toExpr___main(x_26, x_2, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_List_mapM___main___at_Lean_Meta_DepElim_Pattern_toExpr___main___spec__1(x_27, x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
lean_dec(x_2);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_43 = x_28;
} else {
 lean_dec_ref(x_28);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_toExpr___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_mkFVar(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_List_mapM___main___at_Lean_Meta_DepElim_Pattern_toExpr___main___spec__1(x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_mkConst(x_7, x_8);
x_15 = l_List_append___rarg(x_9, x_13);
x_16 = l_List_redLength___main___rarg(x_15);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
x_18 = l_List_toArrayAux___main___rarg(x_15, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_18, x_18, x_19, x_14);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = l_Lean_mkConst(x_7, x_8);
x_24 = l_List_append___rarg(x_9, x_21);
x_25 = l_List_redLength___main___rarg(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
x_27 = l_List_toArrayAux___main___rarg(x_24, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_27, x_27, x_28, x_23);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
case 4:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
lean_inc(x_2);
x_37 = l_List_mapM___main___at_Lean_Meta_DepElim_Pattern_toExpr___main___spec__1(x_36, x_2, x_3);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_mkArrayLit(x_35, x_38, x_2, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
lean_dec(x_2);
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
case 5:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_1 = x_45;
goto _start;
}
default: 
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_3);
return x_48;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_toExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DepElim_Pattern_toExpr___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_FVarSubst_apply(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_9, x_1);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
return x_2;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
case 2:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_19 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1(x_1, x_17);
x_20 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2(x_1, x_18);
lean_ctor_set(x_2, 3, x_20);
lean_ctor_set(x_2, 2, x_19);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1(x_1, x_23);
x_26 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2(x_1, x_24);
x_27 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
}
case 3:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = l_Lean_Meta_FVarSubst_apply(x_1, x_29);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
x_32 = l_Lean_Meta_FVarSubst_apply(x_1, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
case 4:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = l_Lean_Meta_FVarSubst_apply(x_1, x_35);
x_38 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3(x_1, x_36);
lean_ctor_set(x_2, 1, x_38);
lean_ctor_set(x_2, 0, x_37);
return x_2;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = l_Lean_Meta_FVarSubst_apply(x_1, x_39);
x_42 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3(x_1, x_40);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
default: 
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_45, x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_46);
lean_ctor_set(x_2, 1, x_48);
return x_2;
}
else
{
lean_dec(x_47);
lean_free_object(x_2);
lean_dec(x_45);
x_2 = x_46;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_2);
x_52 = l_Std_AssocList_find_x3f___main___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_50, x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_51);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_dec(x_52);
lean_dec(x_50);
x_2 = x_51;
goto _start;
}
}
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Pattern_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = l_Lean_Meta_FVarSubst_insert(x_4, x_1, x_2);
x_6 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Alt_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_Inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Alt_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DepElim_Alt_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":(");
return x_1;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",ctorName:");
return x_1;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_LocalDecl_toExpr(x_4);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_LocalDecl_type(x_4);
lean_dec(x_4);
lean_inc(x_10);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_expr_dbg_to_string(x_10);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__6;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Expr_ctorName(x_10);
lean_dec(x_10);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1(x_5);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = l_Lean_LocalDecl_toExpr(x_26);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_LocalDecl_type(x_26);
lean_dec(x_26);
lean_inc(x_32);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_expr_dbg_to_string(x_32);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__6;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Expr_ctorName(x_32);
lean_dec(x_32);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_4);
x_7 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Meta_DepElim_Pattern_toMessageData___main(x_8);
x_11 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" |- ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Alt_toMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Alt_toMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___main___at_Lean_Meta_DiscrTree_Trie_format___main___spec__2___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_Alt_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1(x_4);
x_6 = l_Lean_MessageData_ofList(x_5);
lean_dec(x_5);
x_7 = l_Lean_Meta_DepElim_Alt_toMessageData___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__2(x_9);
x_11 = l_Lean_MessageData_ofList(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_DepElim_Alt_toMessageData___closed__4;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_addContext___boxed), 3, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_withExistingLocalDecls___rarg(x_4, x_18, x_2, x_3);
return x_19;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Alt_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_4);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1(x_1, x_5);
x_9 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2(x_1, x_6);
lean_ctor_set(x_2, 3, x_9);
lean_ctor_set(x_2, 2, x_8);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_14 = l_Lean_Meta_FVarSubst_apply(x_1, x_11);
x_15 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1(x_1, x_12);
x_16 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2(x_1, x_13);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Meta_DepElim_Alt_applyFVarSubst___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Alt_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DepElim_Alt_applyFVarSubst(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_filterAux___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_LocalDecl_fvarId(x_6);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l_Lean_LocalDecl_fvarId(x_12);
x_15 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_8 = l_Lean_Meta_DepElim_replaceFVarIdAtLocalDecl(x_1, x_2, x_6);
x_9 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = l_Lean_Meta_DepElim_replaceFVarIdAtLocalDecl(x_1, x_2, x_10);
x_13 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_DepElim_Pattern_replaceFVarId(x_1, x_2, x_6);
x_9 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__3(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_DepElim_Pattern_replaceFVarId(x_1, x_2, x_10);
x_13 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__3(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Alt_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_1);
x_8 = l_Lean_Expr_replaceFVarId(x_5, x_1, x_2);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = l_List_filterAux___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__1(x_1, x_6, x_9);
lean_inc(x_1);
x_11 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2(x_1, x_2, x_10);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__3(x_1, x_2, x_7);
lean_ctor_set(x_3, 3, x_12);
lean_ctor_set(x_3, 2, x_11);
lean_ctor_set(x_3, 1, x_8);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_1);
x_17 = l_Lean_Expr_replaceFVarId(x_14, x_1, x_2);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_List_filterAux___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__1(x_1, x_15, x_18);
lean_inc(x_1);
x_20 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2(x_1, x_2, x_19);
x_21 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__3(x_1, x_2, x_16);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
return x_22;
}
}
}
lean_object* l_List_filterAux___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at_Lean_Meta_DepElim_Alt_replaceFVarId___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_1, x_2, x_6);
x_9 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_1, x_2, x_10);
x_13 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_1, x_2, x_6);
x_9 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_1, x_2, x_10);
x_13 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_name_eq(x_4, x_1);
lean_dec(x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
case 2:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1(x_1, x_2, x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
case 4:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2(x_1, x_2, x_14);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2(x_1, x_2, x_16);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at_Lean_Meta_DepElim_Example_replaceFVarId___main___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_DepElim_Example_replaceFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DepElim_Example_replaceFVarId(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_FVarSubst_get(x_1, x_4);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; 
lean_dec(x_5);
lean_free_object(x_2);
x_7 = lean_box(1);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Meta_FVarSubst_get(x_1, x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(1);
return x_12;
}
}
}
case 2:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1(x_1, x_14);
lean_ctor_set(x_2, 1, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1(x_1, x_17);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
case 4:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2(x_1, x_21);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2(x_1, x_23);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
default: 
{
return x_2;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Meta_DepElim_Example_applyFVarSubst___main___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_Example_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_DepElim_Example_applyFVarSubst(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Meta_DepElim_Example_varsToUnderscore___main(x_4);
x_7 = l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Meta_DepElim_Example_varsToUnderscore___main(x_8);
x_11 = l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Example_varsToUnderscore___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(1);
return x_2;
}
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(x_7);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 4:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(x_11);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_List_map___main___at_Lean_Meta_DepElim_Example_varsToUnderscore___main___spec__1(x_13);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
default: 
{
return x_1;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Example_varsToUnderscore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DepElim_Example_varsToUnderscore___main(x_1);
return x_2;
}
}
lean_object* l_List_foldl___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Meta_DepElim_Example_toMessageData___main(x_3);
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Meta_DepElim_Example_toMessageData___main(x_4);
x_7 = l_List_map___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Meta_DepElim_Example_toMessageData___main(x_8);
x_11 = l_List_map___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Meta_DepElim_Example_toMessageData___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkHole___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Example_toMessageData___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Example_toMessageData___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Example_toMessageData___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_arrayHasFormat___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_Example_toMessageData___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_mkFVar(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DepElim_Example_toMessageData___main___closed__2;
return x_5;
}
case 2:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_7, x_8);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_Lean_mkConst(x_11, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__5;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_MessageData_Inhabited___closed__1;
x_18 = l_List_foldl___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__1(x_17, x_6);
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
case 3:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_List_map___main___at_Lean_Meta_DepElim_Example_toMessageData___main___spec__2(x_24);
x_26 = l_Lean_MessageData_ofList(x_25);
lean_dec(x_25);
x_27 = l_Lean_Meta_DepElim_Example_toMessageData___main___closed__3;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Example_toMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DepElim_Example_toMessageData___main(x_1);
return x_2;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_examplesToMessageData___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Meta_DepElim_Example_varsToUnderscore___main(x_4);
x_7 = l_Lean_Meta_DepElim_Example_toMessageData___main(x_6);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_examplesToMessageData___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_DepElim_Example_varsToUnderscore___main(x_9);
x_12 = l_Lean_Meta_DepElim_Example_toMessageData___main(x_11);
x_13 = l_List_map___main___at_Lean_Meta_DepElim_examplesToMessageData___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_examplesToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_map___main___at_Lean_Meta_DepElim_examplesToMessageData___spec__1(x_1);
x_3 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_4 = l_Lean_MessageData_joinSep___main(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_DepElim_withGoalOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Meta_getMVarDecl(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 4);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Meta_withLocalContext___rarg(x_9, x_10, x_2, x_3, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_withGoalOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_withGoalOf___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_withGoalOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DepElim_withGoalOf___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Problem_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Problem_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DepElim_Problem_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_9 = l_Lean_Meta_DepElim_Alt_toMessageData(x_7, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__1(x_8, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_free_object(x_1);
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
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_2);
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
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_2);
x_28 = l_Lean_Meta_DepElim_Alt_toMessageData(x_26, x_2, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__1(x_27, x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
lean_dec(x_2);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_43 = x_28;
} else {
 lean_dec_ref(x_28);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_7);
x_9 = l_Lean_Meta_inferType(x_7, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__2(x_8, x_2, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_free_object(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
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
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_33);
x_35 = l_Lean_Meta_inferType(x_33, x_2, x_3);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_39 = l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__2(x_34, x_2, x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_46);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_44);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_53 = x_45;
} else {
 lean_dec_ref(x_45);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_2);
x_55 = lean_ctor_get(x_35, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_35, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_57 = x_35;
} else {
 lean_dec_ref(x_35);
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
lean_object* _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("vars ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("examples: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__2(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_MessageData_ofList(x_8);
lean_dec(x_8);
x_10 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_MessageData_ofList___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_MessageData_joinSep___main(x_2, x_12);
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
x_17 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__6;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lean_Meta_DepElim_examplesToMessageData(x_19);
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = l_Lean_MessageData_ofList(x_23);
lean_dec(x_23);
x_26 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_MessageData_ofList___closed__3;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_joinSep___main(x_2, x_28);
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__6;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Meta_DepElim_examplesToMessageData(x_35);
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_List_mapM___main___at_Lean_Meta_DepElim_Problem_toMessageData___spec__1), 3, 1);
lean_closure_set(x_5, 0, x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_Meta_DepElim_withGoalOf___rarg(x_1, x_7, x_2, x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_DepElim_Problem_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DepElim_Problem_toMessageData(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_DepElim_counterExampleToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_DepElim_examplesToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_counterExamplesToMessageData___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Meta_DepElim_examplesToMessageData(x_4);
x_7 = l_List_map___main___at_Lean_Meta_DepElim_counterExamplesToMessageData___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Meta_DepElim_examplesToMessageData(x_8);
x_11 = l_List_map___main___at_Lean_Meta_DepElim_counterExamplesToMessageData___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_counterExamplesToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_map___main___at_Lean_Meta_DepElim_counterExamplesToMessageData___spec__1(x_1);
x_3 = l_Lean_MessageData_ofList___closed__3;
x_4 = l_Lean_MessageData_joinSep___main(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthAux___main___rarg(x_7, x_8);
x_10 = lean_nat_dec_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
return x_6;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("incorrect number of patterns");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = 0;
x_7 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___spec__1(x_5, x_6, x_2);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__3;
x_11 = lean_box(0);
x_12 = l_Lean_Meta_throwOther___rarg(x_10, x_11, x_3, x_4);
return x_12;
}
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_LocalDecl_toExpr(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
lean_inc(x_3);
x_13 = l_Lean_Meta_DepElim_Pattern_toExpr___main(x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = x_14;
x_19 = lean_array_fset(x_11, x_1, x_18);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Meta_instantiateLocalDeclMVars(x_7, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3(x_8, x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = l_Lean_Meta_instantiateLocalDeclMVars(x_18, x_2, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3(x_19, x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_6, x_1);
x_8 = l_Lean_Meta_mkForall(x_2, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Array_isEmpty___rarg(x_1);
lean_inc(x_10);
x_14 = lean_array_push(x_2, x_10);
x_15 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3(x_3, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_1, x_1, x_18, x_10);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
x_22 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg(x_7, x_8, x_21, x_14, x_9, x_11, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l_Lean_unitToExpr___lambda__1___closed__3;
x_26 = l_Lean_mkApp(x_10, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
x_29 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg(x_7, x_8, x_28, x_14, x_9, x_11, x_24);
return x_29;
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EqnCompiler");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_12__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchDebug");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2;
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("minor premise ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_List_reverse___rarg(x_3);
x_9 = lean_apply_4(x_5, x_8, x_4, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = l_List_redLength___main___rarg(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
lean_inc(x_12);
x_15 = l_List_toArrayAux___main___rarg(x_12, x_14);
x_16 = x_15;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__1(x_17, x_16);
x_19 = x_18;
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l_List_redLength___main___rarg(x_20);
x_22 = lean_mk_empty_array_with_capacity(x_21);
lean_dec(x_21);
lean_inc(x_20);
x_23 = l_List_toArrayAux___main___rarg(x_20, x_22);
x_24 = x_23;
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__2), 4, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_24);
x_26 = x_25;
lean_inc(x_19);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_19);
x_28 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_inc(x_6);
lean_inc(x_12);
x_29 = l_Lean_Meta_withExistingLocalDecls___rarg(x_12, x_28, x_6, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_isForall(x_30);
x_33 = l_List_lengthAux___main___rarg(x_3, x_17);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_33, x_34);
x_36 = l_Lean_Meta_caseValue___closed__2;
x_37 = l_Lean_Name_appendIndexAfter(x_36, x_35);
x_38 = lean_ctor_get(x_31, 4);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1);
lean_dec(x_38);
if (x_32 == 0)
{
lean_object* x_66; 
x_66 = l_Lean_mkThunkType(x_30);
x_40 = x_66;
goto block_65;
}
else
{
x_40 = x_30;
goto block_65;
}
block_65:
{
if (x_39 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2___boxed), 12, 9);
lean_closure_set(x_41, 0, x_19);
lean_closure_set(x_41, 1, x_4);
lean_closure_set(x_41, 2, x_12);
lean_closure_set(x_41, 3, x_33);
lean_closure_set(x_41, 4, x_20);
lean_closure_set(x_41, 5, x_3);
lean_closure_set(x_41, 6, x_1);
lean_closure_set(x_41, 7, x_11);
lean_closure_set(x_41, 8, x_5);
x_42 = 0;
x_43 = l_Lean_Meta_withLocalDecl___rarg(x_37, x_40, x_42, x_41, x_6, x_31);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4;
x_45 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_44, x_6, x_31);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2___boxed), 12, 9);
lean_closure_set(x_49, 0, x_19);
lean_closure_set(x_49, 1, x_4);
lean_closure_set(x_49, 2, x_12);
lean_closure_set(x_49, 3, x_33);
lean_closure_set(x_49, 4, x_20);
lean_closure_set(x_49, 5, x_3);
lean_closure_set(x_49, 6, x_1);
lean_closure_set(x_49, 7, x_11);
lean_closure_set(x_49, 8, x_5);
x_50 = 0;
x_51 = l_Lean_Meta_withLocalDecl___rarg(x_37, x_40, x_50, x_49, x_6, x_48);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_dec(x_45);
lean_inc(x_37);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_37);
x_54 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__7;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_40);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_40);
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_44, x_59, x_6, x_52);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2___boxed), 12, 9);
lean_closure_set(x_62, 0, x_19);
lean_closure_set(x_62, 1, x_4);
lean_closure_set(x_62, 2, x_12);
lean_closure_set(x_62, 3, x_33);
lean_closure_set(x_62, 4, x_20);
lean_closure_set(x_62, 5, x_3);
lean_closure_set(x_62, 6, x_1);
lean_closure_set(x_62, 7, x_11);
lean_closure_set(x_62, 8, x_5);
x_63 = 0;
x_64 = l_Lean_Meta_withLocalDecl___rarg(x_37, x_40, x_63, x_62, x_6, x_61);
return x_64;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_29);
if (x_67 == 0)
{
return x_29;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_29, 0);
x_69 = lean_ctor_get(x_29, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_29);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___rarg), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg(x_1, x_2, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_assignGoalOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_assignExprMVar___boxed), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
x_7 = l_Lean_Meta_DepElim_withGoalOf___rarg(x_1, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_DepElim_assignGoalOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_DepElim_assignGoalOf(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_4__isDone(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_isEmpty___rarg(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_4__isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_4__isDone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_5__isNextVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_5__isNextVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_5__isNextVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_7) == 5)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
return x_5;
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
return x_5;
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_7) == 3)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
return x_5;
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
x_9 = l_Lean_Expr_isNatLit(x_8);
if (x_9 == 0)
{
return x_5;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
return x_5;
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
return x_5;
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_7) == 4)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
return x_5;
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___spec__1(x_1, x_6);
switch (lean_obj_tag(x_7)) {
case 0:
{
return x_8;
}
case 1:
{
return x_8;
}
default: 
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 1;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___spec__1(x_1, x_2, x_7);
switch (lean_obj_tag(x_8)) {
case 3:
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
case 4:
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
case 5:
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
default: 
{
if (x_1 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
return x_9;
}
}
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_7__hasCtorPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = 1;
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___spec__1(x_2, x_5, x_4);
return x_6;
}
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___spec__1(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___spec__1(x_1, x_2, x_7);
switch (lean_obj_tag(x_8)) {
case 1:
{
if (x_1 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
return x_9;
}
}
case 3:
{
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
return x_9;
}
}
default: 
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = l___private_Lean_Meta_EqnCompiler_DepElim_8__hasValPattern(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = 1;
x_8 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___spec__1(x_4, x_7, x_6);
return x_8;
}
}
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___spec__1(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___spec__1(x_1, x_2, x_7);
switch (lean_obj_tag(x_8)) {
case 1:
{
if (x_1 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
return x_9;
}
}
case 4:
{
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
return x_9;
}
}
default: 
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_11__hasArrayLitPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = l___private_Lean_Meta_EqnCompiler_DepElim_10__hasVarPattern(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = 1;
x_8 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___spec__1(x_4, x_7, x_6);
return x_8;
}
}
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___spec__1(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 3);
if (lean_obj_tag(x_7) == 0)
{
return x_6;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
switch (lean_obj_tag(x_8)) {
case 0:
{
if (x_1 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
case 2:
{
if (x_1 == 0)
{
return x_6;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
default: 
{
return x_6;
}
}
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_9__hasNatValPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = 0;
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___spec__1(x_2, x_5, x_4);
return x_6;
}
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___spec__1(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable___spec__1(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_13 = l_unreachable_x21___rarg(x_12);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
uint8_t x_14; 
lean_free_object(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_4, 3, x_15);
lean_ctor_set(x_10, 1, x_11);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_24 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable___spec__1(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_25 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_26 = l_unreachable_x21___rarg(x_25);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_1);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc(x_36);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 x_37 = x_31;
} else {
 lean_dec_ref(x_31);
 x_37 = lean_box(0);
}
x_38 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable___spec__1(x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_40 = l_unreachable_x21___rarg(x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_44 = lean_alloc_ctor(0, 4, 0);
} else {
 x_44 = x_37;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_42);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Meta_DepElim_Problem_Inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable___spec__1(x_6);
lean_ctor_set(x_1, 2, x_9);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable___spec__1(x_11);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_12);
return x_15;
}
}
}
}
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 1, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_array_get_size(x_1);
x_15 = lean_usize_of_nat(x_12);
x_16 = lean_usize_modn(x_15, x_14);
lean_dec(x_14);
x_17 = lean_array_uget(x_1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_uset(x_1, x_16, x_18);
x_1 = x_19;
x_2 = x_13;
goto _start;
}
}
}
}
lean_object* l_Std_HashSetImp_moveEntries___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__4(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_Std_HashSetImp_expand___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashSetImp_moveEntries___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__3(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_dec_eq(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_nat_dec_eq(x_9, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5(x_10, x_2, x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
}
}
lean_object* l_Std_HashSetImp_insert___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_2);
x_8 = lean_usize_modn(x_7, x_6);
x_9 = lean_array_uget(x_5, x_8);
x_10 = l_List_elem___main___at_Lean_Occurrences_contains___spec__1(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_array_uset(x_5, x_8, x_13);
x_15 = lean_nat_dec_le(x_12, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_1);
x_16 = l_Std_HashSetImp_expand___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__2(x_12, x_14);
return x_16;
}
else
{
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_inc(x_2);
x_17 = l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5(x_9, x_2, x_2);
lean_dec(x_2);
x_18 = lean_array_uset(x_5, x_8, x_17);
lean_ctor_set(x_1, 1, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_2);
x_23 = lean_usize_modn(x_22, x_21);
x_24 = lean_array_uget(x_20, x_23);
x_25 = l_List_elem___main___at_Lean_Occurrences_contains___spec__1(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_19, x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_uset(x_20, x_23, x_28);
x_30 = lean_nat_dec_le(x_27, x_21);
lean_dec(x_21);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Std_HashSetImp_expand___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__2(x_27, x_29);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_inc(x_2);
x_33 = l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5(x_24, x_2, x_2);
lean_dec(x_2);
x_34 = lean_array_uset(x_20, x_23, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = 1;
x_8 = l_Lean_Meta_admit(x_6, x_7, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_2, 1, x_14);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_27 = x_2;
} else {
 lean_dec_ref(x_2);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_5, 0);
lean_inc(x_38);
lean_dec(x_5);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = l_Lean_Meta_DepElim_assignGoalOf(x_1, x_39, x_3, x_4);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l_Std_HashSetImp_insert___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__1(x_44, x_45);
lean_ctor_set(x_2, 0, x_46);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_2);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
lean_dec(x_38);
x_52 = l_Std_HashSetImp_insert___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__1(x_49, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_40, 0, x_55);
return x_40;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_59 = x_2;
} else {
 lean_dec_ref(x_2);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_38, 0);
lean_inc(x_60);
lean_dec(x_38);
x_61 = l_Std_HashSetImp_insert___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__1(x_57, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_56);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_38);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_40);
if (x_66 == 0)
{
return x_40;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_40, 0);
x_68 = lean_ctor_get(x_40, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_40);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
lean_object* l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___main___at___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern___spec__1(x_1, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
lean_ctor_set(x_2, 1, x_11);
return x_2;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 5)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_5, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_21);
x_22 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_20, x_1, x_5);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_5, 3, x_26);
x_27 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_24, x_1, x_5);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_29 = x_10;
} else {
 lean_dec_ref(x_10);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set(x_33, 2, x_9);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_30, x_1, x_33);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_free_object(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_10, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_10, 0);
lean_dec(x_37);
lean_ctor_set(x_10, 1, x_11);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_38; 
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 3);
lean_inc(x_44);
lean_inc(x_1);
x_45 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern___spec__1(x_1, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_1);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 5)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(0, 4, 0);
} else {
 x_54 = x_48;
}
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_43);
lean_ctor_set(x_54, 3, x_53);
x_55 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_51, x_1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_45);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_47);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_1);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_39);
lean_ctor_set(x_58, 1, x_45);
return x_58;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Meta_DepElim_Problem_Inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern___spec__1(x_8, x_6);
lean_ctor_set(x_1, 2, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern___spec__1(x_13, x_11);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_12);
return x_15;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_1);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable___spec__1(x_1, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_14 = l_unreachable_x21___rarg(x_13);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; 
lean_free_object(x_2);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_16; 
lean_dec(x_15);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
lean_ctor_set(x_5, 3, x_17);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
lean_ctor_set(x_5, 3, x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
case 1:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_5, 3, x_22);
x_25 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_24, x_1, x_5);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
lean_ctor_set(x_5, 3, x_26);
x_28 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_27, x_1, x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
default: 
{
uint8_t x_30; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_11, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_11, 0);
lean_dec(x_32);
x_33 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_34 = l_unreachable_x21___rarg(x_33);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_34);
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
x_35 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_36 = l_unreachable_x21___rarg(x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
x_41 = lean_ctor_get(x_5, 2);
x_42 = lean_ctor_get(x_5, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
lean_inc(x_1);
x_43 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable___spec__1(x_1, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_1);
x_44 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_45 = l_unreachable_x21___rarg(x_44);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_45);
return x_2;
}
else
{
lean_object* x_46; 
lean_free_object(x_2);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
switch (lean_obj_tag(x_46)) {
case 0:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_1);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_41);
lean_ctor_set(x_49, 3, x_47);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
case 1:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_52 = x_42;
} else {
 lean_dec_ref(x_42);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set(x_54, 3, x_51);
x_55 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_53, x_1, x_54);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_1);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
x_58 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_59 = l_unreachable_x21___rarg(x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_43);
return x_60;
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
lean_inc(x_1);
x_68 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable___spec__1(x_1, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
x_69 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_70 = l_unreachable_x21___rarg(x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
switch (lean_obj_tag(x_72)) {
case 0:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_1);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_75 = lean_alloc_ctor(0, 4, 0);
} else {
 x_75 = x_67;
}
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_65);
lean_ctor_set(x_75, 3, x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
case 1:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_66, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec(x_72);
if (lean_is_scalar(x_67)) {
 x_80 = lean_alloc_ctor(0, 4, 0);
} else {
 x_80 = x_67;
}
lean_ctor_set(x_80, 0, x_63);
lean_ctor_set(x_80, 1, x_64);
lean_ctor_set(x_80, 2, x_65);
lean_ctor_set(x_80, 3, x_77);
x_81 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_79, x_1, x_80);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_68);
return x_82;
}
default: 
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_72);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_83 = x_66;
} else {
 lean_dec_ref(x_66);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_85 = l_unreachable_x21___rarg(x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_68);
return x_86;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Meta_DepElim_Problem_Inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable___spec__1(x_8, x_6);
lean_ctor_set(x_1, 2, x_10);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable___spec__1(x_14, x_12);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_13);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_21__throwInductiveTypeExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lean_indentExpr(x_7);
x_9 = l___private_Lean_Meta_Tactic_Cases_1__throwInductiveTypeExpected___rarg___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_MessageData_ofList___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_KernelException_toMessageData___closed__12;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_5);
x_16 = l_Lean_indentExpr(x_15);
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_throwOther___rarg(x_17, x_18, x_2, x_6);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_21__throwInductiveTypeExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_21__throwInductiveTypeExpected___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(x_1, x_2, x_5);
x_7 = l_Lean_LocalDecl_fvarId(x_4);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_isAltVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = 0;
x_7 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(x_1, x_6, x_2);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_isAltVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_DepElim_Unify_isAltVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_expandIfVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Meta_FVarSubst_apply(x_3, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
lean_object* l_Lean_Meta_DepElim_Unify_expandIfVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_DepElim_Unify_expandIfVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; size_t x_102; size_t x_103; lean_object* x_104; size_t x_105; uint8_t x_106; 
x_102 = lean_ptr_addr(x_3);
x_103 = x_2 == 0 ? 0 : x_102 % x_2;
x_104 = lean_array_uget(x_4, x_103);
x_105 = lean_ptr_addr(x_104);
lean_dec(x_104);
x_106 = x_105 == x_102;
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
lean_inc(x_3);
x_107 = lean_array_uset(x_4, x_103, x_3);
x_108 = 0;
x_5 = x_108;
x_6 = x_107;
goto block_101;
}
else
{
uint8_t x_109; 
x_109 = 1;
x_5 = x_109;
x_6 = x_4;
goto block_101;
}
block_101:
{
lean_object* x_7; 
if (x_5 == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_3, 0);
lean_inc(x_93);
x_94 = lean_name_eq(x_1, x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_7 = x_95;
goto block_92;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_3);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_6);
return x_97;
}
}
else
{
lean_object* x_98; 
x_98 = lean_box(0);
x_7 = x_98;
goto block_92;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_3);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_6);
return x_100;
}
block_92:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(x_1, x_2, x_8, x_6);
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
x_26 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(x_1, x_2, x_24, x_6);
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
x_42 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(x_1, x_2, x_40, x_6);
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
x_59 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(x_1, x_2, x_56, x_6);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(x_1, x_2, x_57, x_61);
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
}
}
}
uint8_t l_Lean_Meta_DepElim_Unify_occurs(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_FindImpl_initCache;
x_5 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(x_1, x_3, x_2, x_4);
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
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Meta_DepElim_Unify_occurs___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_occurs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_DepElim_Unify_occurs(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Meta_addContext(x_2, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 4);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_11);
x_18 = l_Std_PersistentArray_push___rarg(x_16, x_17);
lean_ctor_set(x_9, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_11);
x_24 = l_Std_PersistentArray_push___rarg(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set(x_8, 4, x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = lean_ctor_get(x_8, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_33 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_35 = x_9;
} else {
 lean_dec_ref(x_9);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_11);
x_37 = l_Std_PersistentArray_push___rarg(x_34, x_36);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_33);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_32);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_7, 1, x_39);
lean_ctor_set(x_7, 0, x_41);
return x_7;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_8, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_8, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 5);
lean_inc(x_47);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 x_48 = x_8;
} else {
 lean_dec_ref(x_8);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_50 = lean_ctor_get(x_9, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_51 = x_9;
} else {
 lean_dec_ref(x_9);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_42);
x_53 = l_Std_PersistentArray_push___rarg(x_50, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_49);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 6, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_44);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_47);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchUnify");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2;
x_2 = l_Lean_Meta_DepElim_Unify_assign___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assign failed variable is not local, ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Unify_assign___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Unify_assign___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assign occurs check failed, ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Unify_assign___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_assign___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Unify_assign___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_assign(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_2);
x_7 = l_Lean_Meta_DepElim_Unify_occurs(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Meta_DepElim_Unify_isAltVar(x_1, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_8);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_25 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_24, x_5, x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
lean_ctor_set(x_25, 0, x_9);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_free_object(x_9);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lean_mkFVar(x_1);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Meta_DepElim_Unify_assign___closed__5;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_2);
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_24, x_40, x_3, x_22, x_5, x_32);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_10);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_41, 0, x_47);
return x_41;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_dec(x_9);
x_55 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_56 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_55, x_5, x_13);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_54);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = l_Lean_mkFVar(x_1);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_Meta_DepElim_Unify_assign___closed__5;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_2);
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_55, x_71, x_3, x_54, x_5, x_63);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_76);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_8, 1);
lean_inc(x_80);
lean_dec(x_8);
x_81 = lean_ctor_get(x_80, 4);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_81, sizeof(void*)*1);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_9, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_84 = x_9;
} else {
 lean_dec_ref(x_9);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_10);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_9, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_88 = x_9;
} else {
 lean_dec_ref(x_9);
 x_88 = lean_box(0);
}
x_89 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_90 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_89, x_5, x_80);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_88;
}
lean_ctor_set(x_95, 0, x_10);
lean_ctor_set(x_95, 1, x_87);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_88);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_dec(x_90);
x_98 = l_Lean_mkFVar(x_1);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Lean_Meta_DepElim_Unify_assign___closed__5;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_2);
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_89, x_105, x_3, x_87, x_5, x_97);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_111 = x_107;
} else {
 lean_dec_ref(x_107);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_10);
lean_ctor_set(x_112, 1, x_110);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
return x_113;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_8, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_115 = x_8;
} else {
 lean_dec_ref(x_8);
 x_115 = lean_box(0);
}
x_116 = !lean_is_exclusive(x_9);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_157; uint8_t x_158; 
x_117 = lean_ctor_get(x_9, 0);
lean_dec(x_117);
x_157 = lean_ctor_get(x_114, 4);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_157, sizeof(void*)*1);
lean_dec(x_157);
if (x_158 == 0)
{
uint8_t x_159; lean_object* x_160; 
x_159 = 0;
x_160 = lean_box(x_159);
lean_ctor_set(x_9, 0, x_160);
x_118 = x_9;
x_119 = x_114;
goto block_156;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_162 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_161, x_5, x_114);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_ctor_set(x_9, 0, x_163);
x_118 = x_9;
x_119 = x_164;
goto block_156;
}
block_156:
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_118);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_118, 1);
x_124 = lean_ctor_get(x_118, 0);
lean_dec(x_124);
x_125 = l_Lean_Meta_FVarSubst_insert(x_123, x_1, x_2);
lean_ctor_set(x_118, 1, x_125);
lean_ctor_set(x_118, 0, x_10);
if (lean_is_scalar(x_115)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_115;
}
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_119);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_118, 1);
lean_inc(x_127);
lean_dec(x_118);
x_128 = l_Lean_Meta_FVarSubst_insert(x_127, x_1, x_2);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_10);
lean_ctor_set(x_129, 1, x_128);
if (lean_is_scalar(x_115)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_115;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_119);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_115);
x_131 = lean_ctor_get(x_118, 1);
lean_inc(x_131);
lean_dec(x_118);
lean_inc(x_1);
x_132 = l_Lean_mkFVar(x_1);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_inc(x_2);
x_136 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_136, 0, x_2);
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_139 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_138, x_137, x_3, x_131, x_5, x_119);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 1);
x_144 = lean_ctor_get(x_141, 0);
lean_dec(x_144);
x_145 = l_Lean_Meta_FVarSubst_insert(x_143, x_1, x_2);
lean_ctor_set(x_141, 1, x_145);
lean_ctor_set(x_141, 0, x_10);
return x_139;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = l_Lean_Meta_FVarSubst_insert(x_146, x_1, x_2);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_10);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_139, 0, x_148);
return x_139;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_139, 0);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_139);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = l_Lean_Meta_FVarSubst_insert(x_151, x_1, x_2);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_10);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_150);
return x_155;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_193; uint8_t x_194; 
x_165 = lean_ctor_get(x_9, 1);
lean_inc(x_165);
lean_dec(x_9);
x_193 = lean_ctor_get(x_114, 4);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_193, sizeof(void*)*1);
lean_dec(x_193);
if (x_194 == 0)
{
uint8_t x_195; lean_object* x_196; lean_object* x_197; 
x_195 = 0;
x_196 = lean_box(x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_165);
x_166 = x_197;
x_167 = x_114;
goto block_192;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_199 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_198, x_5, x_114);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_165);
x_166 = x_202;
x_167 = x_201;
goto block_192;
}
block_192:
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_171 = x_166;
} else {
 lean_dec_ref(x_166);
 x_171 = lean_box(0);
}
x_172 = l_Lean_Meta_FVarSubst_insert(x_170, x_1, x_2);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_10);
lean_ctor_set(x_173, 1, x_172);
if (lean_is_scalar(x_115)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_115;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_115);
x_175 = lean_ctor_get(x_166, 1);
lean_inc(x_175);
lean_dec(x_166);
lean_inc(x_1);
x_176 = l_Lean_mkFVar(x_1);
x_177 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_179 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
lean_inc(x_2);
x_180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_180, 0, x_2);
x_181 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_183 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_182, x_181, x_3, x_175, x_5, x_167);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_188 = x_184;
} else {
 lean_dec_ref(x_184);
 x_188 = lean_box(0);
}
x_189 = l_Lean_Meta_FVarSubst_insert(x_187, x_1, x_2);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_10);
lean_ctor_set(x_190, 1, x_189);
if (lean_is_scalar(x_186)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_186;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_185);
return x_191;
}
}
}
}
}
else
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_6, 4);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_203, sizeof(void*)*1);
lean_dec(x_203);
if (x_204 == 0)
{
uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_2);
lean_dec(x_1);
x_205 = 0;
x_206 = lean_box(x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_4);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_6);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_210 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_209, x_5, x_6);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_unbox(x_211);
lean_dec(x_211);
if (x_212 == 0)
{
uint8_t x_213; 
lean_dec(x_2);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_210);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_210, 0);
lean_dec(x_214);
x_215 = 0;
x_216 = lean_box(x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_4);
lean_ctor_set(x_210, 0, x_217);
return x_210;
}
else
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_210, 1);
lean_inc(x_218);
lean_dec(x_210);
x_219 = 0;
x_220 = lean_box(x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_4);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_210, 1);
lean_inc(x_223);
lean_dec(x_210);
x_224 = l_Lean_mkFVar(x_1);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = l_Lean_Meta_DepElim_Unify_assign___closed__8;
x_227 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__8;
x_229 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_230, 0, x_2);
x_231 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_209, x_231, x_3, x_4, x_5, x_223);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_232, 0);
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_234, 0);
lean_dec(x_236);
x_237 = 0;
x_238 = lean_box(x_237);
lean_ctor_set(x_234, 0, x_238);
return x_232;
}
else
{
lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_dec(x_234);
x_240 = 0;
x_241 = lean_box(x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
lean_ctor_set(x_232, 0, x_242);
return x_232;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_232, 0);
x_244 = lean_ctor_get(x_232, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_232);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = 0;
x_248 = lean_box(x_247);
if (lean_is_scalar(x_246)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_246;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_245);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_244);
return x_250;
}
}
}
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_assign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_DepElim_Unify_assign(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_unify___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unify failed @");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_unify___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Unify_unify___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_Unify_unify___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_Unify_unify___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_unify___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_383; lean_object* x_384; lean_object* x_436; uint8_t x_437; 
x_436 = lean_ctor_get(x_6, 4);
lean_inc(x_436);
x_437 = lean_ctor_get_uint8(x_436, sizeof(void*)*1);
lean_dec(x_436);
if (x_437 == 0)
{
uint8_t x_438; lean_object* x_439; lean_object* x_440; 
x_438 = 0;
x_439 = lean_box(x_438);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_4);
x_383 = x_440;
x_384 = x_6;
goto block_435;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_441 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_442 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_441, x_5, x_6);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_4);
x_383 = x_445;
x_384 = x_444;
goto block_435;
}
block_382:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_DepElim_Unify_expandIfVar(x_1, x_3, x_11, x_5, x_8);
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
lean_inc(x_2);
x_17 = l_Lean_Meta_DepElim_Unify_expandIfVar(x_2, x_3, x_16, x_5, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_expr_eqv(x_1, x_15);
if (x_24 == 0)
{
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_22;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = lean_expr_eqv(x_2, x_22);
if (x_26 == 0)
{
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_22;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_15);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = l_Lean_Meta_DepElim_Unify_assign(x_28, x_2, x_3, x_23, x_5, x_21);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Meta_DepElim_Unify_assign(x_29, x_1, x_3, x_35, x_5, x_34);
lean_dec(x_5);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_30, 0, x_42);
return x_30;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_45 = x_31;
} else {
 lean_dec_ref(x_31);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
case 10:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_2 = x_48;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
default: 
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = l_Lean_Meta_DepElim_Unify_assign(x_50, x_2, x_3, x_23, x_5, x_21);
lean_dec(x_5);
return x_51;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
lean_dec(x_2);
x_53 = l_Lean_Meta_DepElim_Unify_assign(x_52, x_1, x_3, x_23, x_5, x_21);
lean_dec(x_5);
return x_53;
}
case 5:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_dec(x_2);
lean_inc(x_5);
x_58 = l_Lean_Meta_DepElim_Unify_unify___main(x_54, x_56, x_3, x_23, x_5, x_21);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
uint8_t x_62; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_58, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
return x_58;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_58, 0, x_67);
return x_58;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_dec(x_58);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_60);
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
lean_dec(x_58);
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_dec(x_59);
x_1 = x_55;
x_2 = x_57;
x_4 = x_74;
x_6 = x_73;
goto _start;
}
}
else
{
uint8_t x_76; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_58);
if (x_76 == 0)
{
return x_58;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_58, 0);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_58);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 10:
{
lean_object* x_80; 
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
lean_dec(x_2);
x_2 = x_80;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
default: 
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_21, 4);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_82, sizeof(void*)*1);
lean_dec(x_82);
if (x_83 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_19, 0, x_9);
return x_17;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_free_object(x_17);
x_84 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_85 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_84, x_5, x_21);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
uint8_t x_88; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_85);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_85, 0);
lean_dec(x_89);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_85, 0, x_19);
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
lean_ctor_set(x_19, 0, x_9);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_19);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_free_object(x_19);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_1);
x_94 = l_Lean_Meta_DepElim_Unify_unify___main___closed__3;
x_95 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_97 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_98, 0, x_2);
x_99 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_84, x_99, x_3, x_23, x_5, x_92);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set(x_102, 0, x_9);
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_9);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_100, 0, x_106);
return x_100;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_100, 0);
x_108 = lean_ctor_get(x_100, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_100);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_9);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
}
}
}
}
}
case 10:
{
lean_object* x_113; 
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
lean_dec(x_1);
x_1 = x_113;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_115; lean_object* x_116; 
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
x_115 = lean_ctor_get(x_2, 0);
lean_inc(x_115);
lean_dec(x_2);
x_116 = l_Lean_Meta_DepElim_Unify_assign(x_115, x_1, x_3, x_23, x_5, x_21);
lean_dec(x_5);
return x_116;
}
case 10:
{
lean_object* x_117; 
lean_free_object(x_19);
lean_free_object(x_17);
lean_dec(x_9);
x_117 = lean_ctor_get(x_2, 1);
lean_inc(x_117);
lean_dec(x_2);
x_2 = x_117;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
default: 
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_21, 4);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_119, sizeof(void*)*1);
lean_dec(x_119);
if (x_120 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_19, 0, x_9);
return x_17;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_free_object(x_17);
x_121 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_122 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_121, x_5, x_21);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
uint8_t x_125; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_122, 0);
lean_dec(x_126);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_122, 0, x_19);
return x_122;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_dec(x_122);
lean_ctor_set(x_19, 0, x_9);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_19);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_free_object(x_19);
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_dec(x_122);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_1);
x_131 = l_Lean_Meta_DepElim_Unify_unify___main___closed__3;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_2);
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_121, x_136, x_3, x_23, x_5, x_129);
lean_dec(x_5);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_139, 0);
lean_dec(x_141);
lean_ctor_set(x_139, 0, x_9);
return x_137;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_9);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_137, 0, x_143);
return x_137;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_137, 0);
x_145 = lean_ctor_get(x_137, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_137);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_9);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
return x_149;
}
}
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
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_17, 1);
x_151 = lean_ctor_get(x_19, 0);
x_152 = lean_ctor_get(x_19, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_19);
x_153 = lean_expr_eqv(x_1, x_15);
if (x_153 == 0)
{
lean_free_object(x_17);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_151;
x_4 = x_152;
x_6 = x_150;
goto _start;
}
else
{
uint8_t x_155; 
x_155 = lean_expr_eqv(x_2, x_151);
if (x_155 == 0)
{
lean_free_object(x_17);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_151;
x_4 = x_152;
x_6 = x_150;
goto _start;
}
else
{
lean_dec(x_151);
lean_dec(x_15);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_free_object(x_17);
lean_dec(x_9);
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_2, 0);
lean_inc(x_158);
x_159 = l_Lean_Meta_DepElim_Unify_assign(x_157, x_2, x_3, x_152, x_5, x_150);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_161);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = l_Lean_Meta_DepElim_Unify_assign(x_158, x_1, x_3, x_164, x_5, x_163);
lean_dec(x_5);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_158);
lean_dec(x_5);
lean_dec(x_1);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_167 = x_159;
} else {
 lean_dec_ref(x_159);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_160, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_168);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_167;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
return x_171;
}
}
case 10:
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_2, 1);
lean_inc(x_172);
lean_dec(x_2);
x_2 = x_172;
x_4 = x_152;
x_6 = x_150;
goto _start;
}
default: 
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
lean_dec(x_1);
x_175 = l_Lean_Meta_DepElim_Unify_assign(x_174, x_2, x_3, x_152, x_5, x_150);
lean_dec(x_5);
return x_175;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_176; lean_object* x_177; 
lean_free_object(x_17);
lean_dec(x_9);
x_176 = lean_ctor_get(x_2, 0);
lean_inc(x_176);
lean_dec(x_2);
x_177 = l_Lean_Meta_DepElim_Unify_assign(x_176, x_1, x_3, x_152, x_5, x_150);
lean_dec(x_5);
return x_177;
}
case 5:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_free_object(x_17);
lean_dec(x_9);
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 1);
lean_inc(x_179);
lean_dec(x_1);
x_180 = lean_ctor_get(x_2, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 1);
lean_inc(x_181);
lean_dec(x_2);
lean_inc(x_5);
x_182 = l_Lean_Meta_DepElim_Unify_unify___main(x_178, x_180, x_3, x_152, x_5, x_150);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_5);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_189 = x_183;
} else {
 lean_dec_ref(x_183);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_184);
lean_ctor_set(x_190, 1, x_188);
if (lean_is_scalar(x_187)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_187;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_186);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_184);
x_192 = lean_ctor_get(x_182, 1);
lean_inc(x_192);
lean_dec(x_182);
x_193 = lean_ctor_get(x_183, 1);
lean_inc(x_193);
lean_dec(x_183);
x_1 = x_179;
x_2 = x_181;
x_4 = x_193;
x_6 = x_192;
goto _start;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_5);
x_195 = lean_ctor_get(x_182, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_182, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_197 = x_182;
} else {
 lean_dec_ref(x_182);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
case 10:
{
lean_object* x_199; 
lean_free_object(x_17);
lean_dec(x_9);
x_199 = lean_ctor_get(x_2, 1);
lean_inc(x_199);
lean_dec(x_2);
x_2 = x_199;
x_4 = x_152;
x_6 = x_150;
goto _start;
}
default: 
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_150, 4);
lean_inc(x_201);
x_202 = lean_ctor_get_uint8(x_201, sizeof(void*)*1);
lean_dec(x_201);
if (x_202 == 0)
{
lean_object* x_203; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_9);
lean_ctor_set(x_203, 1, x_152);
lean_ctor_set(x_17, 0, x_203);
return x_17;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_free_object(x_17);
x_204 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_205 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_204, x_5, x_150);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_unbox(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_209 = x_205;
} else {
 lean_dec_ref(x_205);
 x_209 = lean_box(0);
}
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_9);
lean_ctor_set(x_210, 1, x_152);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
lean_dec(x_205);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_1);
x_214 = l_Lean_Meta_DepElim_Unify_unify___main___closed__3;
x_215 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_217 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_218, 0, x_2);
x_219 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_204, x_219, x_3, x_152, x_5, x_212);
lean_dec(x_5);
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
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_9);
lean_ctor_set(x_226, 1, x_224);
if (lean_is_scalar(x_223)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_223;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_222);
return x_227;
}
}
}
}
}
case 10:
{
lean_object* x_228; 
lean_free_object(x_17);
lean_dec(x_9);
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
lean_dec(x_1);
x_1 = x_228;
x_4 = x_152;
x_6 = x_150;
goto _start;
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_230; lean_object* x_231; 
lean_free_object(x_17);
lean_dec(x_9);
x_230 = lean_ctor_get(x_2, 0);
lean_inc(x_230);
lean_dec(x_2);
x_231 = l_Lean_Meta_DepElim_Unify_assign(x_230, x_1, x_3, x_152, x_5, x_150);
lean_dec(x_5);
return x_231;
}
case 10:
{
lean_object* x_232; 
lean_free_object(x_17);
lean_dec(x_9);
x_232 = lean_ctor_get(x_2, 1);
lean_inc(x_232);
lean_dec(x_2);
x_2 = x_232;
x_4 = x_152;
x_6 = x_150;
goto _start;
}
default: 
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_150, 4);
lean_inc(x_234);
x_235 = lean_ctor_get_uint8(x_234, sizeof(void*)*1);
lean_dec(x_234);
if (x_235 == 0)
{
lean_object* x_236; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_9);
lean_ctor_set(x_236, 1, x_152);
lean_ctor_set(x_17, 0, x_236);
return x_17;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_free_object(x_17);
x_237 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_238 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_237, x_5, x_150);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_242 = x_238;
} else {
 lean_dec_ref(x_238);
 x_242 = lean_box(0);
}
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_9);
lean_ctor_set(x_243, 1, x_152);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_245 = lean_ctor_get(x_238, 1);
lean_inc(x_245);
lean_dec(x_238);
x_246 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_246, 0, x_1);
x_247 = l_Lean_Meta_DepElim_Unify_unify___main___closed__3;
x_248 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_250 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_251, 0, x_2);
x_252 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_237, x_252, x_3, x_152, x_5, x_245);
lean_dec(x_5);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_258 = x_254;
} else {
 lean_dec_ref(x_254);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_9);
lean_ctor_set(x_259, 1, x_257);
if (lean_is_scalar(x_256)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_256;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_255);
return x_260;
}
}
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
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_261 = lean_ctor_get(x_17, 0);
x_262 = lean_ctor_get(x_17, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_17);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_265 = x_261;
} else {
 lean_dec_ref(x_261);
 x_265 = lean_box(0);
}
x_266 = lean_expr_eqv(x_1, x_15);
if (x_266 == 0)
{
lean_dec(x_265);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_263;
x_4 = x_264;
x_6 = x_262;
goto _start;
}
else
{
uint8_t x_268; 
x_268 = lean_expr_eqv(x_2, x_263);
if (x_268 == 0)
{
lean_dec(x_265);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_263;
x_4 = x_264;
x_6 = x_262;
goto _start;
}
else
{
lean_dec(x_263);
lean_dec(x_15);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_dec(x_265);
lean_dec(x_9);
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_270 = lean_ctor_get(x_1, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_2, 0);
lean_inc(x_271);
x_272 = l_Lean_Meta_DepElim_Unify_assign(x_270, x_2, x_3, x_264, x_5, x_262);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_unbox(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_274);
x_276 = lean_ctor_get(x_272, 1);
lean_inc(x_276);
lean_dec(x_272);
x_277 = lean_ctor_get(x_273, 1);
lean_inc(x_277);
lean_dec(x_273);
x_278 = l_Lean_Meta_DepElim_Unify_assign(x_271, x_1, x_3, x_277, x_5, x_276);
lean_dec(x_5);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_271);
lean_dec(x_5);
lean_dec(x_1);
x_279 = lean_ctor_get(x_272, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_280 = x_272;
} else {
 lean_dec_ref(x_272);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_273, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_282 = x_273;
} else {
 lean_dec_ref(x_273);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_274);
lean_ctor_set(x_283, 1, x_281);
if (lean_is_scalar(x_280)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_280;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_279);
return x_284;
}
}
case 10:
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_2, 1);
lean_inc(x_285);
lean_dec(x_2);
x_2 = x_285;
x_4 = x_264;
x_6 = x_262;
goto _start;
}
default: 
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_1, 0);
lean_inc(x_287);
lean_dec(x_1);
x_288 = l_Lean_Meta_DepElim_Unify_assign(x_287, x_2, x_3, x_264, x_5, x_262);
lean_dec(x_5);
return x_288;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_265);
lean_dec(x_9);
x_289 = lean_ctor_get(x_2, 0);
lean_inc(x_289);
lean_dec(x_2);
x_290 = l_Lean_Meta_DepElim_Unify_assign(x_289, x_1, x_3, x_264, x_5, x_262);
lean_dec(x_5);
return x_290;
}
case 5:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_265);
lean_dec(x_9);
x_291 = lean_ctor_get(x_1, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_1, 1);
lean_inc(x_292);
lean_dec(x_1);
x_293 = lean_ctor_get(x_2, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_2, 1);
lean_inc(x_294);
lean_dec(x_2);
lean_inc(x_5);
x_295 = l_Lean_Meta_DepElim_Unify_unify___main(x_291, x_293, x_3, x_264, x_5, x_262);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_unbox(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_294);
lean_dec(x_292);
lean_dec(x_5);
x_299 = lean_ctor_get(x_295, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_300 = x_295;
} else {
 lean_dec_ref(x_295);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_296, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_302 = x_296;
} else {
 lean_dec_ref(x_296);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_297);
lean_ctor_set(x_303, 1, x_301);
if (lean_is_scalar(x_300)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_300;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_299);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_297);
x_305 = lean_ctor_get(x_295, 1);
lean_inc(x_305);
lean_dec(x_295);
x_306 = lean_ctor_get(x_296, 1);
lean_inc(x_306);
lean_dec(x_296);
x_1 = x_292;
x_2 = x_294;
x_4 = x_306;
x_6 = x_305;
goto _start;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_294);
lean_dec(x_292);
lean_dec(x_5);
x_308 = lean_ctor_get(x_295, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_295, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_310 = x_295;
} else {
 lean_dec_ref(x_295);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
case 10:
{
lean_object* x_312; 
lean_dec(x_265);
lean_dec(x_9);
x_312 = lean_ctor_get(x_2, 1);
lean_inc(x_312);
lean_dec(x_2);
x_2 = x_312;
x_4 = x_264;
x_6 = x_262;
goto _start;
}
default: 
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_262, 4);
lean_inc(x_314);
x_315 = lean_ctor_get_uint8(x_314, sizeof(void*)*1);
lean_dec(x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_265)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_265;
}
lean_ctor_set(x_316, 0, x_9);
lean_ctor_set(x_316, 1, x_264);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_262);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_318 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_319 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_318, x_5, x_262);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_unbox(x_320);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_323 = x_319;
} else {
 lean_dec_ref(x_319);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_265;
}
lean_ctor_set(x_324, 0, x_9);
lean_ctor_set(x_324, 1, x_264);
if (lean_is_scalar(x_323)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_323;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_322);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_265);
x_326 = lean_ctor_get(x_319, 1);
lean_inc(x_326);
lean_dec(x_319);
x_327 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_327, 0, x_1);
x_328 = l_Lean_Meta_DepElim_Unify_unify___main___closed__3;
x_329 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_331 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_332, 0, x_2);
x_333 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_318, x_333, x_3, x_264, x_5, x_326);
lean_dec(x_5);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_339 = x_335;
} else {
 lean_dec_ref(x_335);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_9);
lean_ctor_set(x_340, 1, x_338);
if (lean_is_scalar(x_337)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_337;
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_336);
return x_341;
}
}
}
}
}
case 10:
{
lean_object* x_342; 
lean_dec(x_265);
lean_dec(x_9);
x_342 = lean_ctor_get(x_1, 1);
lean_inc(x_342);
lean_dec(x_1);
x_1 = x_342;
x_4 = x_264;
x_6 = x_262;
goto _start;
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_265);
lean_dec(x_9);
x_344 = lean_ctor_get(x_2, 0);
lean_inc(x_344);
lean_dec(x_2);
x_345 = l_Lean_Meta_DepElim_Unify_assign(x_344, x_1, x_3, x_264, x_5, x_262);
lean_dec(x_5);
return x_345;
}
case 10:
{
lean_object* x_346; 
lean_dec(x_265);
lean_dec(x_9);
x_346 = lean_ctor_get(x_2, 1);
lean_inc(x_346);
lean_dec(x_2);
x_2 = x_346;
x_4 = x_264;
x_6 = x_262;
goto _start;
}
default: 
{
lean_object* x_348; uint8_t x_349; 
x_348 = lean_ctor_get(x_262, 4);
lean_inc(x_348);
x_349 = lean_ctor_get_uint8(x_348, sizeof(void*)*1);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_265)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_265;
}
lean_ctor_set(x_350, 0, x_9);
lean_ctor_set(x_350, 1, x_264);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_262);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_352 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_353 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_352, x_5, x_262);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_unbox(x_354);
lean_dec(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_357 = x_353;
} else {
 lean_dec_ref(x_353);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_265;
}
lean_ctor_set(x_358, 0, x_9);
lean_ctor_set(x_358, 1, x_264);
if (lean_is_scalar(x_357)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_357;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_356);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_265);
x_360 = lean_ctor_get(x_353, 1);
lean_inc(x_360);
lean_dec(x_353);
x_361 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_361, 0, x_1);
x_362 = l_Lean_Meta_DepElim_Unify_unify___main___closed__3;
x_363 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_365 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_366, 0, x_2);
x_367 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
x_368 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_352, x_367, x_3, x_264, x_5, x_360);
lean_dec(x_5);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_371 = x_368;
} else {
 lean_dec_ref(x_368);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_373 = x_369;
} else {
 lean_dec_ref(x_369);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_9);
lean_ctor_set(x_374, 1, x_372);
if (lean_is_scalar(x_371)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_371;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_370);
return x_375;
}
}
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
uint8_t x_376; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_7);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_7, 0);
lean_dec(x_377);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_7);
lean_ctor_set(x_378, 1, x_8);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_7, 1);
lean_inc(x_379);
lean_dec(x_7);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_9);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_8);
return x_381;
}
}
}
block_435:
{
lean_object* x_385; uint8_t x_386; 
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
x_386 = lean_unbox(x_385);
lean_dec(x_385);
if (x_386 == 0)
{
uint8_t x_387; 
x_387 = !lean_is_exclusive(x_383);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_383, 1);
x_389 = lean_ctor_get(x_383, 0);
lean_dec(x_389);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_390 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_5, x_384);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
lean_ctor_set(x_383, 0, x_391);
x_7 = x_383;
x_8 = x_392;
goto block_382;
}
else
{
uint8_t x_393; 
lean_free_object(x_383);
lean_dec(x_388);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_390);
if (x_393 == 0)
{
return x_390;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_390, 0);
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_390);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_383, 1);
lean_inc(x_397);
lean_dec(x_383);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_398 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_5, x_384);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_397);
x_7 = x_401;
x_8 = x_400;
goto block_382;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_397);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_402 = lean_ctor_get(x_398, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_398, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_404 = x_398;
} else {
 lean_dec_ref(x_398);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_403);
return x_405;
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_406 = lean_ctor_get(x_383, 1);
lean_inc(x_406);
lean_dec(x_383);
lean_inc(x_1);
x_407 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_407, 0, x_1);
x_408 = l_Lean_Meta_Exception_toTraceMessageData___closed__51;
x_409 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
lean_inc(x_2);
x_410 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_410, 0, x_2);
x_411 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_413 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_DepElim_Unify_assign___spec__1(x_412, x_411, x_3, x_406, x_5, x_384);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = !lean_is_exclusive(x_414);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_414, 1);
x_418 = lean_ctor_get(x_414, 0);
lean_dec(x_418);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_419 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_5, x_415);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
lean_ctor_set(x_414, 0, x_420);
x_7 = x_414;
x_8 = x_421;
goto block_382;
}
else
{
uint8_t x_422; 
lean_free_object(x_414);
lean_dec(x_417);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_422 = !lean_is_exclusive(x_419);
if (x_422 == 0)
{
return x_419;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_419, 0);
x_424 = lean_ctor_get(x_419, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_419);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_414, 1);
lean_inc(x_426);
lean_dec(x_414);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_427 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_5, x_415);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_426);
x_7 = x_430;
x_8 = x_429;
goto block_382;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_426);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_431 = lean_ctor_get(x_427, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_427, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_433 = x_427;
} else {
 lean_dec_ref(x_427);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
}
}
}
}
lean_object* l_Lean_Meta_DepElim_Unify_unify___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_DepElim_Unify_unify___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_unify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_DepElim_Unify_unify___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_DepElim_Unify_unify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_DepElim_Unify_unify(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_23__unify_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Meta_instantiateMVars(x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_instantiateMVars(x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_DepElim_Unify_unify___main(x_7, x_10, x_1, x_12, x_4, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
uint8_t x_31; 
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
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_23__unify_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_EqnCompiler_DepElim_23__unify_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = l_Lean_Expr_fvarId_x21(x_12);
lean_dec(x_12);
lean_inc(x_3);
x_14 = l_Lean_Meta_getLocalDecl(x_13, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
x_19 = x_15;
x_20 = lean_array_fset(x_11, x_1, x_19);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_20;
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_LocalDecl_fvarId(x_6);
x_9 = l_Std_AssocList_contains___main___at_Lean_Meta_FVarSubst_contains___spec__1(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l_Lean_LocalDecl_fvarId(x_12);
x_15 = l_Std_AssocList_contains___main___at_Lean_Meta_FVarSubst_contains___spec__1(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Pattern_applyFVarSubst___main(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_9 = l_Lean_Meta_FVarSubst_get(x_1, x_8);
x_10 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(x_1, x_2, x_7);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = 0;
x_13 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(x_11, x_12, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = l_Lean_Expr_fvarId_x21(x_17);
lean_dec(x_17);
x_20 = l_Lean_Meta_FVarSubst_get(x_1, x_19);
x_21 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(x_1, x_2, x_18);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = 0;
x_24 = l_List_foldr___main___at___private_Lean_Meta_EqnCompiler_DepElim_22__inLocalDecls___spec__1(x_22, x_23, x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_5, x_5, x_9, x_1);
lean_inc(x_3);
x_11 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_2, x_10, x_3);
lean_inc(x_5);
x_12 = x_5;
x_13 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__1), 4, 2);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_12);
x_14 = x_13;
lean_inc(x_7);
x_15 = lean_apply_2(x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_19 = lean_ctor_get(x_11, 2);
lean_inc(x_19);
x_20 = l_List_append___rarg(x_18, x_19);
x_21 = l___private_Lean_Meta_EqnCompiler_DepElim_23__unify_x3f(x_20, x_6, x_4, x_7, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_box(0);
x_34 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2(x_32, x_20, x_33);
x_35 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(x_32, x_34);
x_36 = lean_ctor_get(x_11, 3);
lean_inc(x_36);
x_37 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(x_32, x_36);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = l_Lean_Meta_FVarSubst_apply(x_32, x_38);
x_40 = l_Array_toList___rarg(x_5);
lean_dec(x_5);
x_41 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(x_32, x_35, x_40);
lean_dec(x_32);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
lean_dec(x_3);
x_43 = l_List_append___rarg(x_41, x_37);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_22, 0, x_44);
return x_21;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_22, 0);
lean_inc(x_45);
lean_dec(x_22);
x_46 = lean_box(0);
x_47 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2(x_45, x_20, x_46);
x_48 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(x_45, x_47);
x_49 = lean_ctor_get(x_11, 3);
lean_inc(x_49);
x_50 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(x_45, x_49);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_dec(x_11);
x_52 = l_Lean_Meta_FVarSubst_apply(x_45, x_51);
x_53 = l_Array_toList___rarg(x_5);
lean_dec(x_5);
x_54 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(x_45, x_48, x_53);
lean_dec(x_45);
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
lean_dec(x_3);
x_56 = l_List_append___rarg(x_54, x_50);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_48);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_21, 0, x_58);
return x_21;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
lean_dec(x_21);
x_60 = lean_ctor_get(x_22, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_61 = x_22;
} else {
 lean_dec_ref(x_22);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
x_63 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2(x_60, x_20, x_62);
x_64 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(x_60, x_63);
x_65 = lean_ctor_get(x_11, 3);
lean_inc(x_65);
x_66 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(x_60, x_65);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_dec(x_11);
x_68 = l_Lean_Meta_FVarSubst_apply(x_60, x_67);
x_69 = l_Array_toList___rarg(x_5);
lean_dec(x_5);
x_70 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(x_60, x_64, x_69);
lean_dec(x_60);
x_71 = lean_ctor_get(x_3, 0);
lean_inc(x_71);
lean_dec(x_3);
x_72 = l_List_append___rarg(x_70, x_66);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_64);
lean_ctor_set(x_73, 3, x_72);
if (lean_is_scalar(x_61)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_61;
}
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_59);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_21);
if (x_76 == 0)
{
return x_21;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_21, 0);
x_78 = lean_ctor_get(x_21, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_21);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_15);
if (x_80 == 0)
{
return x_15;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_15, 0);
x_82 = lean_ctor_get(x_15, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_15);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Meta_getLocalDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_1);
x_9 = l_Lean_mkFVar(x_1);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType(x_9, x_5, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
x_13 = l_Lean_Meta_whnfD(x_11, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_14);
x_16 = l_Lean_Meta_getInductiveUniverseAndParams(x_14, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_21 = l_Lean_mkConst(x_2, x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_20, x_20, x_22, x_21);
lean_dec(x_20);
lean_inc(x_5);
lean_inc(x_23);
x_24 = l_Lean_Meta_inferType(x_23, x_5, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__1), 8, 4);
lean_closure_set(x_27, 0, x_23);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_14);
x_28 = l_Lean_Meta_forallTelescopeReducing___rarg(x_25, x_27, x_5, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
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
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
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
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getEnv___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__2___boxed), 6, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_1);
x_8 = l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = l_Lean_Meta_withExistingLocalDecls___rarg(x_6, x_9, x_4, x_5);
return x_10;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__2(x_5);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_box(1);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__2(x_11);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_Expr_fvarId_x21(x_1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 1);
x_11 = l_Array_toList___rarg(x_10);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__2(x_11);
lean_inc(x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_8, x_14, x_6);
lean_dec(x_14);
lean_dec(x_8);
x_16 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = l_Lean_Expr_fvarId_x21(x_1);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_20, 1);
x_22 = l_Array_toList___rarg(x_21);
x_23 = lean_ctor_get(x_2, 1);
x_24 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__2(x_22);
lean_inc(x_23);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_19, x_25, x_17);
lean_dec(x_25);
lean_dec(x_19);
x_27 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3(x_1, x_2, x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 2);
x_9 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_8, x_5);
x_10 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4(x_1, x_6);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_13, 2);
x_15 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_14, x_11);
x_16 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
case 1:
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_14;
x_3 = x_6;
goto _start;
}
case 2:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_name_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_free_object(x_6);
lean_dec(x_5);
x_2 = x_16;
goto _start;
}
else
{
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_16;
x_3 = x_6;
goto _start;
}
}
default: 
{
lean_object* x_21; 
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_5);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_3);
x_2 = x_24;
x_3 = x_25;
goto _start;
}
case 1:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_27;
x_3 = x_28;
goto _start;
}
case 2:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_name_eq(x_31, x_1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_dec(x_5);
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_3);
x_2 = x_30;
x_3 = x_34;
goto _start;
}
}
default: 
{
lean_object* x_36; 
lean_dec(x_23);
lean_dec(x_5);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_dec(x_2);
x_2 = x_36;
goto _start;
}
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Alt_applyFVarSubst(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Alt_applyFVarSubst(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__7(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__7(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__7(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inaccessible in ctor step ");
return x_1;
}
}
lean_object* _init_l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_25; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_11 = x_4;
} else {
 lean_dec_ref(x_4);
 x_11 = lean_box(0);
}
x_25 = lean_ctor_get(x_9, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
x_26 = l_Lean_Meta_isClassQuick___main___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
lean_inc(x_6);
x_28 = lean_apply_2(x_27, x_6, x_7);
x_12 = x_28;
goto block_24;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_100; uint8_t x_101; 
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_9, 2);
lean_inc(x_32);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 x_33 = x_9;
} else {
 lean_dec_ref(x_9);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_100 = lean_ctor_get(x_7, 4);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_100, sizeof(void*)*1);
lean_dec(x_100);
if (x_101 == 0)
{
x_36 = x_7;
goto block_99;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_inc(x_1);
x_102 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1, x_6, x_7);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_36 = x_105;
goto block_99;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
lean_inc(x_35);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_35);
x_108 = l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__3;
x_109 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
lean_inc(x_1);
x_110 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_1, x_109, x_6, x_106);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_36 = x_111;
goto block_99;
}
}
block_99:
{
lean_object* x_37; 
lean_inc(x_6);
x_37 = l_Lean_Meta_whnfD(x_35, x_6, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_2);
x_40 = l_Lean_Expr_constructorApp_x3f(x_2, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_41 = lean_box(0);
lean_ctor_set(x_37, 0, x_41);
x_12 = x_37;
goto block_24;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_name_eq(x_47, x_3);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_44);
lean_free_object(x_40);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_49 = lean_box(0);
lean_ctor_set(x_37, 0, x_49);
x_12 = x_37;
goto block_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_array_get_size(x_45);
x_52 = l_Array_extract___rarg(x_45, x_50, x_51);
lean_dec(x_51);
lean_dec(x_45);
x_53 = l_Array_toList___rarg(x_52);
lean_dec(x_52);
x_54 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__7(x_53);
x_55 = l_List_append___rarg(x_54, x_34);
if (lean_is_scalar(x_33)) {
 x_56 = lean_alloc_ctor(0, 4, 0);
} else {
 x_56 = x_33;
}
lean_ctor_set(x_56, 0, x_30);
lean_ctor_set(x_56, 1, x_31);
lean_ctor_set(x_56, 2, x_32);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_40, 0, x_56);
lean_ctor_set(x_37, 0, x_40);
x_12 = x_37;
goto block_24;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_40, 0);
lean_inc(x_57);
lean_dec(x_40);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_name_eq(x_61, x_3);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_63 = lean_box(0);
lean_ctor_set(x_37, 0, x_63);
x_12 = x_37;
goto block_24;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_58, 3);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_array_get_size(x_59);
x_66 = l_Array_extract___rarg(x_59, x_64, x_65);
lean_dec(x_65);
lean_dec(x_59);
x_67 = l_Array_toList___rarg(x_66);
lean_dec(x_66);
x_68 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__7(x_67);
x_69 = l_List_append___rarg(x_68, x_34);
if (lean_is_scalar(x_33)) {
 x_70 = lean_alloc_ctor(0, 4, 0);
} else {
 x_70 = x_33;
}
lean_ctor_set(x_70, 0, x_30);
lean_ctor_set(x_70, 1, x_31);
lean_ctor_set(x_70, 2, x_32);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_37, 0, x_71);
x_12 = x_37;
goto block_24;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_37, 0);
x_73 = lean_ctor_get(x_37, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_37);
lean_inc(x_2);
x_74 = l_Lean_Expr_constructorApp_x3f(x_2, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_12 = x_76;
goto block_24;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_name_eq(x_82, x_3);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_73);
x_12 = x_85;
goto block_24;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_79, 3);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_array_get_size(x_80);
x_88 = l_Array_extract___rarg(x_80, x_86, x_87);
lean_dec(x_87);
lean_dec(x_80);
x_89 = l_Array_toList___rarg(x_88);
lean_dec(x_88);
x_90 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__7(x_89);
x_91 = l_List_append___rarg(x_90, x_34);
if (lean_is_scalar(x_33)) {
 x_92 = lean_alloc_ctor(0, 4, 0);
} else {
 x_92 = x_33;
}
lean_ctor_set(x_92, 0, x_30);
lean_ctor_set(x_92, 1, x_31);
lean_ctor_set(x_92, 2, x_32);
lean_ctor_set(x_92, 3, x_91);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_73);
x_12 = x_94;
goto block_24;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_95 = !lean_is_exclusive(x_37);
if (x_95 == 0)
{
x_12 = x_37;
goto block_24;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_37, 0);
x_97 = lean_ctor_get(x_37, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_37);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_12 = x_98;
goto block_24;
}
}
}
}
case 1:
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_9);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_9, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_25, 1);
lean_inc(x_114);
lean_dec(x_25);
x_115 = lean_ctor_get(x_29, 0);
lean_inc(x_115);
lean_dec(x_29);
lean_ctor_set(x_9, 3, x_114);
lean_inc(x_6);
lean_inc(x_3);
x_116 = l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f(x_9, x_115, x_3, x_6, x_7);
x_12 = x_116;
goto block_24;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_9, 0);
x_118 = lean_ctor_get(x_9, 1);
x_119 = lean_ctor_get(x_9, 2);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_9);
x_120 = lean_ctor_get(x_25, 1);
lean_inc(x_120);
lean_dec(x_25);
x_121 = lean_ctor_get(x_29, 0);
lean_inc(x_121);
lean_dec(x_29);
x_122 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_120);
lean_inc(x_6);
lean_inc(x_3);
x_123 = l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f(x_122, x_121, x_3, x_6, x_7);
x_12 = x_123;
goto block_24;
}
}
case 2:
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_9);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_9, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_25, 1);
lean_inc(x_126);
lean_dec(x_25);
x_127 = lean_ctor_get(x_29, 3);
lean_inc(x_127);
lean_dec(x_29);
x_128 = l_List_append___rarg(x_127, x_126);
lean_ctor_set(x_9, 3, x_128);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_9);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
x_12 = x_130;
goto block_24;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_131 = lean_ctor_get(x_9, 0);
x_132 = lean_ctor_get(x_9, 1);
x_133 = lean_ctor_get(x_9, 2);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_9);
x_134 = lean_ctor_get(x_25, 1);
lean_inc(x_134);
lean_dec(x_25);
x_135 = lean_ctor_get(x_29, 3);
lean_inc(x_135);
lean_dec(x_29);
x_136 = l_List_append___rarg(x_135, x_134);
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_132);
lean_ctor_set(x_137, 2, x_133);
lean_ctor_set(x_137, 3, x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_7);
x_12 = x_139;
goto block_24;
}
}
default: 
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
x_140 = l_Lean_Meta_isClassQuick___main___closed__1;
x_141 = l_unreachable_x21___rarg(x_140);
lean_inc(x_6);
x_142 = lean_apply_2(x_141, x_6, x_7);
x_12 = x_142;
goto block_24;
}
}
}
block_24:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_4 = x_10;
x_7 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
if (lean_is_scalar(x_11)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_11;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_4 = x_10;
x_5 = x_18;
x_7 = x_16;
goto _start;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_lt(x_7, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_8;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_15 = lean_array_fget(x_8, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_8, x_7, x_16);
x_18 = x_15;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Array_toList___rarg(x_21);
lean_dec(x_21);
lean_inc(x_4);
x_24 = l_List_append___rarg(x_23, x_4);
x_25 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1(x_22, x_24);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
x_28 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3(x_3, x_18, x_27);
x_29 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4(x_18, x_28);
lean_dec(x_18);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_box(0);
x_32 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__5(x_26, x_30, x_31);
x_33 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6(x_22, x_32);
lean_dec(x_22);
x_34 = l_List_reverse___rarg(x_33);
lean_inc(x_5);
lean_inc(x_2);
x_35 = lean_alloc_closure((void*)(l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8), 7, 5);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_5);
lean_closure_set(x_35, 2, x_26);
lean_closure_set(x_35, 3, x_34);
lean_closure_set(x_35, 4, x_31);
lean_inc(x_20);
x_36 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___lambda__1___boxed), 6, 3);
lean_closure_set(x_36, 0, x_20);
lean_closure_set(x_36, 1, x_25);
lean_closure_set(x_36, 2, x_29);
x_37 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_getMVarDecl(x_20, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 4);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Lean_Meta_withLocalContext___rarg(x_41, x_42, x_37, x_9, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_7, x_46);
x_48 = x_44;
x_49 = lean_array_fset(x_17, x_7, x_48);
lean_dec(x_7);
x_7 = x_47;
x_8 = x_49;
x_10 = x_45;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
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
lean_dec(x_37);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2;
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor step");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_3, 4);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
if (x_31 == 0)
{
x_4 = x_3;
goto block_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
x_33 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_32, x_2, x_3);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_4 = x_36;
goto block_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__5;
x_39 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_32, x_38, x_2, x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_4 = x_40;
goto block_29;
}
}
block_29:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = l_Lean_Meta_isClassQuick___main___closed__1;
x_7 = l_unreachable_x21___rarg(x_6);
x_8 = lean_apply_2(x_7, x_2, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Expr_fvarId_x21(x_9);
x_14 = l_Array_empty___closed__1;
x_15 = 0;
lean_inc(x_13);
x_16 = l_Lean_Meta_Cases_cases(x_12, x_13, x_14, x_15, x_2, x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = x_17;
x_20 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___boxed), 10, 8);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_9);
lean_closure_set(x_22, 3, x_10);
lean_closure_set(x_22, 4, x_11);
lean_closure_set(x_22, 5, x_13);
lean_closure_set(x_22, 6, x_21);
lean_closure_set(x_22, 7, x_19);
x_23 = x_22;
x_24 = lean_apply_2(x_23, x_2, x_18);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__6(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_1, x_9);
x_1 = x_11;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_9);
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_2 = x_14;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Array_empty___closed__1;
x_4 = l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues___spec__1(x_3, x_2);
return x_4;
}
}
uint8_t l___private_Lean_Meta_EqnCompiler_DepElim_27__isFirstPatternVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_27__isFirstPatternVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_27__isFirstPatternVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__1(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l___private_Lean_Meta_EqnCompiler_DepElim_27__isFirstPatternVar(x_5);
if (x_7 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_EqnCompiler_DepElim_27__isFirstPatternVar(x_10);
if (x_12 == 0)
{
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues(x_1);
x_11 = l_Lean_Expr_fvarId_x21(x_2);
x_12 = lean_array_fget(x_10, x_3);
lean_dec(x_10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_11, x_13, x_8);
lean_dec(x_13);
lean_dec(x_11);
x_15 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2(x_1, x_2, x_3, lean_box(0), x_9);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues(x_1);
x_19 = l_Lean_Expr_fvarId_x21(x_2);
x_20 = lean_array_fget(x_18, x_3);
lean_dec(x_18);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_19, x_21, x_16);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2(x_1, x_2, x_3, lean_box(0), x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_7, x_5);
x_9 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 2);
x_13 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_12, x_10);
x_14 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
switch (lean_obj_tag(x_10)) {
case 1:
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
case 3:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_expr_eqv(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_free_object(x_6);
lean_dec(x_5);
x_2 = x_14;
goto _start;
}
else
{
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_14;
x_3 = x_6;
goto _start;
}
}
default: 
{
lean_object* x_19; 
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_5);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
switch (lean_obj_tag(x_21)) {
case 1:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_3);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_expr_eqv(x_26, x_1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_5);
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_3);
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
default: 
{
lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_5);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_2 = x_31;
goto _start;
}
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Alt_applyFVarSubst(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Alt_applyFVarSubst(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_1);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__6(x_1, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_14 = l_unreachable_x21___rarg(x_13);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; 
lean_free_object(x_2);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
switch (lean_obj_tag(x_15)) {
case 1:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
lean_ctor_set(x_5, 3, x_17);
x_20 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_19, x_1, x_5);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_5, 3, x_21);
x_23 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_22, x_1, x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
case 3:
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 1);
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
lean_ctor_set(x_5, 3, x_26);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
lean_ctor_set(x_5, 3, x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
default: 
{
uint8_t x_30; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_11, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_11, 0);
lean_dec(x_32);
x_33 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_34 = l_unreachable_x21___rarg(x_33);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_34);
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
x_35 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_36 = l_unreachable_x21___rarg(x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
x_41 = lean_ctor_get(x_5, 2);
x_42 = lean_ctor_get(x_5, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
lean_inc(x_1);
x_43 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__6(x_1, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_1);
x_44 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_45 = l_unreachable_x21___rarg(x_44);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_45);
return x_2;
}
else
{
lean_object* x_46; 
lean_free_object(x_2);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
switch (lean_obj_tag(x_46)) {
case 1:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_47);
x_51 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_49, x_1, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
case 3:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
lean_dec(x_1);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 3, x_53);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_1);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
x_58 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_59 = l_unreachable_x21___rarg(x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_43);
return x_60;
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
lean_inc(x_1);
x_68 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__6(x_1, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
x_69 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_70 = l_unreachable_x21___rarg(x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
switch (lean_obj_tag(x_72)) {
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
if (lean_is_scalar(x_67)) {
 x_76 = lean_alloc_ctor(0, 4, 0);
} else {
 x_76 = x_67;
}
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_64);
lean_ctor_set(x_76, 2, x_65);
lean_ctor_set(x_76, 3, x_73);
x_77 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_75, x_1, x_76);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_68);
return x_78;
}
case 3:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_72);
lean_dec(x_1);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_80 = x_66;
} else {
 lean_dec_ref(x_66);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_81 = lean_alloc_ctor(0, 4, 0);
} else {
 x_81 = x_67;
}
lean_ctor_set(x_81, 0, x_63);
lean_ctor_set(x_81, 1, x_64);
lean_ctor_set(x_81, 2, x_65);
lean_ctor_set(x_81, 3, x_79);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_68);
return x_82;
}
default: 
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_72);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_1);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_83 = x_66;
} else {
 lean_dec_ref(x_66);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Meta_DepElim_Alt_Inhabited;
x_85 = l_unreachable_x21___rarg(x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_68);
return x_86;
}
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_lt(x_7, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_8;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_fget(x_8, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_8, x_7, x_16);
x_18 = x_15;
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_7, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
x_23 = lean_box(0);
x_24 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__1(x_21, x_23);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_inc(x_2);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_22);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_7, x_27);
x_29 = x_26;
x_30 = lean_array_fset(x_17, x_7, x_29);
lean_dec(x_7);
x_7 = x_28;
x_8 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_array_fget(x_5, x_7);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_inc(x_1);
x_37 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2(x_1, x_3, x_7, lean_box(0), x_36);
x_38 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3(x_18, x_37);
lean_dec(x_18);
x_39 = lean_box(0);
x_40 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__4(x_32, x_35, x_39);
x_41 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5(x_34, x_40);
x_42 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__6(x_32, x_41);
lean_inc(x_4);
x_43 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7(x_34, x_4);
lean_dec(x_34);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_38);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_7, x_45);
x_47 = x_44;
x_48 = lean_array_fset(x_17, x_7, x_47);
lean_dec(x_7);
x_7 = x_46;
x_8 = x_48;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value step");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_3, 4);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_29 == 0)
{
x_4 = x_3;
goto block_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
x_31 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_30, x_2, x_3);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_4 = x_34;
goto block_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__3;
x_37 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_30, x_36, x_2, x_35);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_4 = x_38;
goto block_27;
}
}
block_27:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = l_Lean_Meta_isClassQuick___main___closed__1;
x_7 = l_unreachable_x21___rarg(x_6);
x_8 = lean_apply_2(x_7, x_2, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_EqnCompiler_DepElim_26__collectValues(x_1);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Expr_fvarId_x21(x_9);
x_14 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_13);
x_15 = l_Lean_Meta_caseValues(x_12, x_13, x_11, x_14, x_2, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = x_16;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__8___boxed), 10, 8);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_5);
lean_closure_set(x_20, 2, x_9);
lean_closure_set(x_20, 3, x_10);
lean_closure_set(x_20, 4, x_11);
lean_closure_set(x_20, 5, x_13);
lean_closure_set(x_20, 6, x_19);
lean_closure_set(x_20, 7, x_18);
x_21 = x_20;
x_22 = lean_apply_2(x_21, x_2, x_17);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___main___rarg(x_9, x_10);
x_12 = l_Array_contains___at___private_Lean_Meta_FunInfo_3__collectDepsAux___main___spec__2(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_1, x_11);
x_1 = x_13;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_11);
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_2, 1);
x_2 = x_16;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Array_empty___closed__1;
x_4 = l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_10 = l_Lean_Meta_getLocalDecl(x_9, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__1(x_8, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_11);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_free_object(x_1);
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
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_29 = l_Lean_Expr_fvarId_x21(x_27);
lean_dec(x_27);
lean_inc(x_2);
x_30 = l_Lean_Meta_getLocalDecl(x_29, x_2, x_3);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__1(x_28, x_2, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_34);
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_31);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_28);
lean_dec(x_2);
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Expr_fvarId_x21(x_4);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__2(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__2(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_push(x_1, x_7);
x_11 = l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main(x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
x_13 = lean_nat_add(x_12, x_11);
lean_inc(x_4);
x_14 = l_Lean_Name_appendIndexAfter(x_4, x_13);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___lambda__1___boxed), 9, 6);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_12);
x_16 = 0;
x_17 = l_Lean_Meta_withLocalDecl___rarg(x_14, x_3, x_16, x_15, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_18 = l_Array_toList___rarg(x_6);
lean_dec(x_6);
lean_inc(x_7);
lean_inc(x_18);
x_19 = l_Lean_Meta_mkArrayLit(x_3, x_18, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_1);
x_22 = l_Lean_Meta_DepElim_Alt_replaceFVarId(x_2, x_20, x_1);
lean_inc(x_18);
x_23 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__1(x_18, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__2(x_18);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 2);
x_30 = lean_ctor_get(x_22, 3);
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = l_List_append___rarg(x_25, x_29);
x_33 = l_List_append___rarg(x_26, x_30);
lean_ctor_set(x_22, 3, x_33);
lean_ctor_set(x_22, 2, x_32);
lean_ctor_set(x_22, 0, x_27);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_22, 1);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_37 = l_List_append___rarg(x_25, x_35);
x_38 = l_List_append___rarg(x_26, x_36);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_23);
x_42 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___spec__2(x_18);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_22, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_22, 3);
lean_inc(x_46);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 x_47 = x_22;
} else {
 lean_dec_ref(x_22);
 x_47 = lean_box(0);
}
x_48 = l_List_append___rarg(x_40, x_45);
x_49 = l_List_append___rarg(x_42, x_46);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 4, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_23);
if (x_52 == 0)
{
return x_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_23);
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
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_LocalDecl_userName(x_5);
x_9 = l_Array_empty___closed__1;
x_10 = l___private_Lean_Meta_EqnCompiler_DepElim_30__expandVarIntoArrayLitAux___main(x_1, x_2, x_3, x_8, x_4, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit___lambda__1___boxed), 7, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_withExistingLocalDecls___rarg(x_7, x_10, x_5, x_6);
return x_11;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_mkFVar(x_4);
x_7 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_mkFVar(x_8);
x_11 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__3(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_Expr_fvarId_x21(x_1);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Array_toList___rarg(x_9);
x_11 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__3(x_10);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_8, x_12, x_6);
lean_dec(x_12);
lean_dec(x_8);
x_14 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = l_Lean_Expr_fvarId_x21(x_1);
x_18 = lean_ctor_get(x_2, 1);
x_19 = l_Array_toList___rarg(x_18);
x_20 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__3(x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_DepElim_Example_replaceFVarId___main(x_17, x_21, x_15);
lean_dec(x_21);
lean_dec(x_17);
x_23 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4(x_1, x_2, x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_7, x_5);
x_9 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Meta_DepElim_Example_applyFVarSubst___main(x_12, x_10);
x_14 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
switch (lean_obj_tag(x_10)) {
case 1:
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
case 4:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_List_lengthAux___main___rarg(x_15, x_16);
lean_dec(x_15);
x_18 = lean_nat_dec_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_free_object(x_6);
lean_dec(x_5);
x_2 = x_14;
goto _start;
}
else
{
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_5);
x_2 = x_14;
x_3 = x_6;
goto _start;
}
}
default: 
{
lean_object* x_21; 
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_5);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_2 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
switch (lean_obj_tag(x_23)) {
case 1:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_3);
x_2 = x_24;
x_3 = x_25;
goto _start;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_List_lengthAux___main___rarg(x_28, x_29);
lean_dec(x_28);
x_31 = lean_nat_dec_eq(x_30, x_1);
lean_dec(x_30);
if (x_31 == 0)
{
lean_dec(x_5);
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_3);
x_2 = x_27;
x_3 = x_33;
goto _start;
}
}
default: 
{
lean_object* x_35; 
lean_dec(x_23);
lean_dec(x_5);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_2 = x_35;
goto _start;
}
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Meta_DepElim_Alt_applyFVarSubst(x_1, x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Meta_DepElim_Alt_applyFVarSubst(x_1, x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_10 = x_3;
} else {
 lean_dec_ref(x_3);
 x_10 = lean_box(0);
}
x_26 = lean_ctor_get(x_8, 3);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
x_27 = l_Lean_Meta_isClassQuick___main___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
lean_inc(x_4);
x_29 = lean_apply_2(x_28, x_4, x_5);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_11 = x_30;
x_12 = x_31;
goto block_25;
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
switch (lean_obj_tag(x_36)) {
case 1:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
x_40 = lean_ctor_get(x_8, 2);
x_41 = lean_ctor_get(x_8, 3);
lean_dec(x_41);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_4);
lean_inc(x_1);
x_44 = l_Lean_Meta_getArrayArgType(x_1, x_4, x_5);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_ctor_set(x_8, 3, x_42);
lean_inc(x_4);
lean_inc(x_2);
x_47 = l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit(x_8, x_43, x_45, x_2, x_4, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_11 = x_48;
x_12 = x_49;
goto block_25;
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
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
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_8);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_44);
if (x_54 == 0)
{
return x_44;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_44, 0);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_44);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_8, 0);
x_59 = lean_ctor_get(x_8, 1);
x_60 = lean_ctor_get(x_8, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_8);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
lean_dec(x_26);
x_62 = lean_ctor_get(x_36, 0);
lean_inc(x_62);
lean_dec(x_36);
lean_inc(x_4);
lean_inc(x_1);
x_63 = l_Lean_Meta_getArrayArgType(x_1, x_4, x_5);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_59);
lean_ctor_set(x_66, 2, x_60);
lean_ctor_set(x_66, 3, x_61);
lean_inc(x_4);
lean_inc(x_2);
x_67 = l___private_Lean_Meta_EqnCompiler_DepElim_31__expandVarIntoArrayLit(x_66, x_62, x_64, x_2, x_4, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_11 = x_68;
x_12 = x_69;
goto block_25;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_ctor_get(x_63, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_76 = x_63;
} else {
 lean_dec_ref(x_63);
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
case 4:
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_8);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_8, 3);
lean_dec(x_79);
x_80 = lean_ctor_get(x_26, 1);
lean_inc(x_80);
lean_dec(x_26);
x_81 = lean_ctor_get(x_36, 1);
lean_inc(x_81);
lean_dec(x_36);
x_82 = l_List_append___rarg(x_81, x_80);
lean_ctor_set(x_8, 3, x_82);
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_8, 0);
x_84 = lean_ctor_get(x_8, 1);
x_85 = lean_ctor_get(x_8, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_8);
x_86 = lean_ctor_get(x_26, 1);
lean_inc(x_86);
lean_dec(x_26);
x_87 = lean_ctor_get(x_36, 1);
lean_inc(x_87);
lean_dec(x_36);
x_88 = l_List_append___rarg(x_87, x_86);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_85);
lean_ctor_set(x_89, 3, x_88);
x_11 = x_89;
x_12 = x_5;
goto block_25;
}
}
default: 
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_8);
x_90 = l_Lean_Meta_isClassQuick___main___closed__1;
x_91 = l_unreachable_x21___rarg(x_90);
lean_inc(x_4);
x_92 = lean_apply_2(x_91, x_4, x_5);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_11 = x_93;
x_12 = x_94;
goto block_25;
}
else
{
uint8_t x_95; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 0);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_92);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
block_25:
{
lean_object* x_13; 
x_13 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__8(x_1, x_2, x_9, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(1, 2, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
if (lean_is_scalar(x_10)) {
 x_19 = lean_alloc_ctor(1, 2, 0);
} else {
 x_19 = x_10;
}
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_lt(x_7, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_8;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_fget(x_8, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_8, x_7, x_16);
x_18 = x_15;
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_7, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
x_23 = lean_box(0);
x_24 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___spec__1(x_21, x_23);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_inc(x_2);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_22);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_7, x_27);
x_29 = x_26;
x_30 = lean_array_fset(x_17, x_7, x_29);
lean_dec(x_7);
x_7 = x_28;
x_8 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = l_Nat_Inhabited;
x_33 = lean_array_get(x_32, x_5, x_7);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_18, 3);
lean_inc(x_36);
x_37 = l_Array_toList___rarg(x_35);
lean_dec(x_35);
x_38 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__1(x_37);
lean_inc(x_4);
x_39 = l_List_append___rarg(x_38, x_4);
x_40 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2(x_36, x_39);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
x_43 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4(x_3, x_18, x_42);
x_44 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5(x_18, x_43);
lean_dec(x_18);
x_45 = lean_box(0);
x_46 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__6(x_33, x_41, x_45);
x_47 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7(x_36, x_46);
lean_dec(x_36);
lean_inc(x_9);
lean_inc(x_3);
x_48 = l_List_mapM___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__8(x_3, x_33, x_47, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_44);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_7, x_52);
x_54 = x_51;
x_55 = lean_array_fset(x_17, x_7, x_54);
lean_dec(x_7);
x_7 = x_53;
x_8 = x_55;
x_10 = x_50;
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
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
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("array literal step");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_3, 4);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
lean_dec(x_29);
if (x_30 == 0)
{
x_4 = x_3;
goto block_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
x_32 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_31, x_2, x_3);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_4 = x_35;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__3;
x_38 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_31, x_37, x_2, x_36);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_4 = x_39;
goto block_28;
}
}
block_28:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = l_Lean_Meta_isClassQuick___main___closed__1;
x_7 = l_unreachable_x21___rarg(x_6);
x_8 = lean_apply_2(x_7, x_2, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = l___private_Lean_Meta_EqnCompiler_DepElim_29__collectArraySizes(x_1);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_Lean_Expr_fvarId_x21(x_9);
x_14 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_15 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_13);
x_16 = l_Lean_Meta_caseArraySizes(x_12, x_13, x_11, x_14, x_15, x_2, x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = x_17;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__9___boxed), 10, 8);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_9);
lean_closure_set(x_21, 3, x_10);
lean_closure_set(x_21, 4, x_11);
lean_closure_set(x_21, 5, x_13);
lean_closure_set(x_21, 6, x_20);
lean_closure_set(x_21, 7, x_19);
x_22 = x_21;
x_23 = lean_apply_2(x_22, x_2, x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* _init_l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__1;
x_3 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1(x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 3)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_13) == 9)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_4, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = l_Lean_mkNatLit(x_27);
lean_ctor_set(x_11, 0, x_29);
lean_ctor_set(x_9, 1, x_28);
x_30 = l_Lean_Meta_evalNat___main___closed__17;
x_31 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_9);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_31);
lean_ctor_set(x_4, 3, x_1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_23);
lean_free_object(x_11);
x_33 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2;
lean_ctor_set(x_9, 0, x_33);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_35, x_38);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = l_Lean_mkNatLit(x_39);
lean_ctor_set(x_11, 0, x_41);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Meta_evalNat___main___closed__17;
x_44 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_40);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set(x_4, 3, x_1);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_10);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_35);
lean_free_object(x_11);
x_46 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_4, 3, x_47);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_4);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_49 = x_9;
} else {
 lean_dec_ref(x_9);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_sub(x_50, x_53);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = l_Lean_mkNatLit(x_54);
lean_ctor_set(x_11, 0, x_56);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Meta_evalNat___main___closed__17;
x_59 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set(x_1, 1, x_48);
lean_ctor_set(x_1, 0, x_59);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_7);
lean_ctor_set(x_60, 2, x_8);
lean_ctor_set(x_60, 3, x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_10);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_50);
lean_free_object(x_11);
x_62 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2;
if (lean_is_scalar(x_49)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_49;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_48);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_6);
lean_ctor_set(x_64, 1, x_7);
lean_ctor_set(x_64, 2, x_8);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_64);
return x_1;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_14);
lean_free_object(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_9, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_9, 0);
lean_dec(x_67);
lean_ctor_set(x_9, 1, x_10);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_68; 
lean_dec(x_9);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_10);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
x_69 = !lean_is_exclusive(x_9);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_9, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_9, 0);
lean_dec(x_71);
lean_ctor_set(x_9, 1, x_10);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_72; 
lean_dec(x_9);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_10);
return x_72;
}
}
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_11, 0);
lean_inc(x_73);
lean_dec(x_11);
if (lean_obj_tag(x_73) == 9)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_75 = x_4;
} else {
 lean_dec_ref(x_4);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_9, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_77 = x_9;
} else {
 lean_dec_ref(x_9);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_sub(x_78, x_81);
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = l_Lean_mkNatLit(x_82);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
x_87 = l_Lean_Meta_evalNat___main___closed__17;
x_88 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
lean_ctor_set(x_88, 2, x_83);
lean_ctor_set(x_88, 3, x_86);
lean_ctor_set(x_1, 1, x_76);
lean_ctor_set(x_1, 0, x_88);
if (lean_is_scalar(x_75)) {
 x_89 = lean_alloc_ctor(0, 4, 0);
} else {
 x_89 = x_75;
}
lean_ctor_set(x_89, 0, x_6);
lean_ctor_set(x_89, 1, x_7);
lean_ctor_set(x_89, 2, x_8);
lean_ctor_set(x_89, 3, x_1);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_10);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_78);
x_91 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2;
if (lean_is_scalar(x_77)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_77;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_76);
if (lean_is_scalar(x_75)) {
 x_93 = lean_alloc_ctor(0, 4, 0);
} else {
 x_93 = x_75;
}
lean_ctor_set(x_93, 0, x_6);
lean_ctor_set(x_93, 1, x_7);
lean_ctor_set(x_93, 2, x_8);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_93);
return x_1;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_94 = x_9;
} else {
 lean_dec_ref(x_9);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_4);
lean_ctor_set(x_95, 1, x_10);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_96 = x_9;
} else {
 lean_dec_ref(x_9);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_4);
lean_ctor_set(x_97, 1, x_10);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
x_98 = !lean_is_exclusive(x_9);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_9, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_9, 0);
lean_dec(x_100);
lean_ctor_set(x_9, 1, x_10);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_101; 
lean_dec(x_9);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_4);
lean_ctor_set(x_101, 1, x_10);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_1, 0);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_1);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_102, 3);
lean_inc(x_107);
x_108 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1(x_103);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_109; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 3)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_obj_tag(x_111) == 9)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 lean_ctor_release(x_102, 3);
 x_114 = x_102;
} else {
 lean_dec_ref(x_102);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_116 = x_107;
} else {
 lean_dec_ref(x_107);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_nat_dec_eq(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_nat_sub(x_117, x_120);
lean_dec(x_117);
x_122 = lean_box(0);
x_123 = l_Lean_mkNatLit(x_121);
if (lean_is_scalar(x_112)) {
 x_124 = lean_alloc_ctor(3, 1, 0);
} else {
 x_124 = x_112;
}
lean_ctor_set(x_124, 0, x_123);
if (lean_is_scalar(x_116)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_116;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
x_126 = l_Lean_Meta_evalNat___main___closed__17;
x_127 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_122);
lean_ctor_set(x_127, 2, x_122);
lean_ctor_set(x_127, 3, x_125);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_115);
if (lean_is_scalar(x_114)) {
 x_129 = lean_alloc_ctor(0, 4, 0);
} else {
 x_129 = x_114;
}
lean_ctor_set(x_129, 0, x_104);
lean_ctor_set(x_129, 1, x_105);
lean_ctor_set(x_129, 2, x_106);
lean_ctor_set(x_129, 3, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_108);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_117);
lean_dec(x_112);
x_131 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2;
if (lean_is_scalar(x_116)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_116;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_115);
if (lean_is_scalar(x_114)) {
 x_133 = lean_alloc_ctor(0, 4, 0);
} else {
 x_133 = x_114;
}
lean_ctor_set(x_133, 0, x_104);
lean_ctor_set(x_133, 1, x_105);
lean_ctor_set(x_133, 2, x_106);
lean_ctor_set(x_133, 3, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_108);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_135 = x_107;
} else {
 lean_dec_ref(x_107);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_102);
lean_ctor_set(x_136, 1, x_108);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_137 = x_107;
} else {
 lean_dec_ref(x_107);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_102);
lean_ctor_set(x_138, 1, x_108);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_110);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_139 = x_107;
} else {
 lean_dec_ref(x_107);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_102);
lean_ctor_set(x_140, 1, x_108);
return x_140;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1(x_3);
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" step");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
x_11 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_10, x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_10, x_26, x_3, x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
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
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_3 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Meta_DepElim_Problem_toMessageData(x_1, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_2, x_9, x_4, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_tracer___closed__3;
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___lambda__1___boxed), 5, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__2;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Lean_Meta_DepElim_withGoalOf___rarg(x_1, x_7, x_2, x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not implement yet ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DepElim_Problem_toMessageData(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_box(0);
x_10 = l_Lean_Meta_throwOther___rarg(x_8, x_9, x_2, x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_12 = l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main(x_11, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_15;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non variable");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nat value to constructor");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variable");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("as-pattern");
return x_1;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_Meta_EqnCompiler_DepElim_4__isDone(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l___private_Lean_Meta_EqnCompiler_DepElim_6__hasAsPattern(x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l___private_Lean_Meta_EqnCompiler_DepElim_5__isNextVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__1;
x_11 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep(x_10, x_2, x_3, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_EqnCompiler_DepElim_17__processNonVariable(x_1);
x_1 = x_15;
x_2 = x_14;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lean_Meta_EqnCompiler_DepElim_12__isVariableTransition(x_1);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l___private_Lean_Meta_EqnCompiler_DepElim_13__isConstructorTransition(x_1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l___private_Lean_Meta_EqnCompiler_DepElim_14__isValueTransition(x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l___private_Lean_Meta_EqnCompiler_DepElim_15__isArrayLitTransition(x_1);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l___private_Lean_Meta_EqnCompiler_DepElim_16__isNatValueTransition(x_1);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_2);
x_22 = l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported(x_1, x_3, x_6);
lean_dec(x_3);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__2;
x_28 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep(x_27, x_2, x_3, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern(x_1);
x_1 = x_32;
x_2 = x_31;
x_4 = x_30;
goto _start;
}
}
else
{
lean_object* x_34; 
lean_inc(x_3);
x_34 = l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit(x_1, x_3, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1(x_35, x_37, x_2, x_3, x_36);
lean_dec(x_35);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_2);
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
}
else
{
lean_object* x_43; 
lean_inc(x_3);
x_43 = l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue(x_1, x_3, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1(x_44, x_46, x_2, x_3, x_45);
lean_dec(x_44);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; 
lean_inc(x_3);
x_52 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor(x_1, x_3, x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1(x_53, x_55, x_2, x_3, x_54);
lean_dec(x_53);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__3;
x_62 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep(x_61, x_2, x_3, x_6);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Lean_Meta_EqnCompiler_DepElim_20__processVariable(x_1);
x_1 = x_66;
x_2 = x_65;
x_4 = x_64;
goto _start;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__4;
x_69 = l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep(x_68, x_2, x_3, x_6);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l___private_Lean_Meta_EqnCompiler_DepElim_19__processAsPattern(x_1);
x_1 = x_73;
x_2 = x_72;
x_4 = x_71;
goto _start;
}
}
else
{
lean_object* x_75; 
x_75 = l___private_Lean_Meta_EqnCompiler_DepElim_18__processLeaf(x_1, x_2, x_3, x_6);
lean_dec(x_3);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_5);
if (x_76 == 0)
{
return x_5;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_5, 0);
x_78 = lean_ctor_get(x_5, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_5);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_37__process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_List_map___main___at_Lean_Meta_DepElim_mkElim___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Expr_fvarId_x21(x_4);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___main___at_Lean_Meta_DepElim_mkElim___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_map___main___at_Lean_Meta_DepElim_mkElim___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Std_mkHashSet___at_Lean_Meta_DepElim_mkElim___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_DepElim_mkElim___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_List_elem___main___at_Lean_Occurrences_contains___spec__1(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_Meta_DepElim_mkElim___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Std_HashSetImp_contains___at_Lean_Meta_DepElim_mkElim___spec__3(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_5);
x_4 = x_9;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_4 = x_9;
goto _start;
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Position_lt___closed__1;
x_2 = lean_alloc_closure((void*)(l_beqOfEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eliminator: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eliminator value: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ntype: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_box(0);
x_12 = 0;
lean_inc(x_9);
lean_inc(x_1);
x_13 = l_Lean_Meta_mkFreshExprMVar(x_1, x_11, x_12, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_toList___rarg(x_2);
lean_inc(x_16);
x_17 = l_List_map___main___at_Lean_Meta_DepElim_mkElim___spec__1(x_16);
x_18 = l_Lean_Expr_mvarId_x21(x_14);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_7);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__3;
lean_inc(x_9);
x_22 = l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main(x_19, x_21, x_9, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_mkOptionalNode___closed__2;
x_27 = lean_array_push(x_26, x_3);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_28, x_27);
x_30 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_8, x_8, x_28, x_29);
lean_inc(x_9);
lean_inc(x_30);
x_31 = l_Lean_Meta_mkForall(x_30, x_1, x_9, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_9);
x_34 = l_Lean_Meta_mkLambda(x_30, x_14, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_75; uint8_t x_76; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_75 = lean_ctor_get(x_36, 4);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_dec(x_75);
if (x_76 == 0)
{
x_37 = x_36;
goto block_74;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_inc(x_6);
x_77 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_6, x_9, x_36);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_37 = x_80;
goto block_74;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
lean_inc(x_35);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_35);
x_83 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__9;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__12;
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_32);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_32);
x_88 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_6);
x_89 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_6, x_88, x_9, x_81);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_37 = x_90;
goto block_74;
}
}
block_74:
{
lean_object* x_38; 
lean_inc(x_9);
lean_inc(x_4);
x_38 = l_Lean_Meta_mkAuxDefinition(x_4, x_32, x_35, x_9, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_51 = 0;
x_52 = l_Lean_Meta_setInlineAttribute(x_4, x_51, x_9, x_40);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 4);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
lean_dec(x_54);
if (x_55 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
x_42 = x_53;
goto block_50;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc(x_6);
x_56 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_6, x_9, x_53);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_9);
lean_dec(x_6);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_42 = x_59;
goto block_50;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
lean_inc(x_39);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_39);
x_62 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__6;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_6, x_63, x_9, x_60);
lean_dec(x_9);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_42 = x_65;
goto block_50;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_6);
x_66 = !lean_is_exclusive(x_52);
if (x_66 == 0)
{
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_52, 0);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_52);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
block_50:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = l_List_lengthAux___main___rarg(x_5, x_28);
x_44 = l_Lean_Meta_DepElim_mkElim___lambda__1___closed__1;
lean_inc(x_43);
x_45 = l_Nat_foldAux___main___at_Lean_Meta_DepElim_mkElim___spec__4(x_44, x_25, x_43, x_43, x_20);
lean_dec(x_43);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_dec(x_25);
x_47 = l_List_reverse___rarg(x_45);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
else
{
uint8_t x_70; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_38);
if (x_70 == 0)
{
return x_38;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_38, 0);
x_72 = lean_ctor_get(x_38, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_38);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_91 = !lean_is_exclusive(x_34);
if (x_91 == 0)
{
return x_34;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_34, 0);
x_93 = lean_ctor_get(x_34, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_34);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_31);
if (x_95 == 0)
{
return x_31;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_31, 0);
x_97 = lean_ctor_get(x_31, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_31);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_22);
if (x_99 == 0)
{
return x_22;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_22, 0);
x_101 = lean_ctor_get(x_22, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_22);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("target: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_DepElim_mkElim___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns(x_4, x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_11 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_10, x_2);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4;
lean_inc(x_1);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_mkElim___lambda__1___boxed), 10, 6);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_1);
lean_closure_set(x_15, 5, x_14);
x_16 = l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts___rarg(x_2, x_1, x_15, x_6, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4;
x_18 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_17, x_6, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_2);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_mkElim___lambda__1___boxed), 10, 6);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_4);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_1);
lean_closure_set(x_22, 5, x_17);
x_23 = l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts___rarg(x_2, x_1, x_22, x_6, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
lean_inc(x_11);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_11);
x_26 = l_Lean_Meta_DepElim_mkElim___lambda__2___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_17, x_27, x_6, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_1);
lean_inc(x_2);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_mkElim___lambda__1___boxed), 10, 6);
lean_closure_set(x_30, 0, x_11);
lean_closure_set(x_30, 1, x_4);
lean_closure_set(x_30, 2, x_2);
lean_closure_set(x_30, 3, x_3);
lean_closure_set(x_30, 4, x_1);
lean_closure_set(x_30, 5, x_17);
x_31 = l___private_Lean_Meta_EqnCompiler_DepElim_3__withAlts___rarg(x_2, x_1, x_30, x_6, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_mkElim___lambda__2___boxed), 7, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_2);
x_8 = l_Lean_Meta_forallTelescopeReducing___rarg(x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElim___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_DepElim_mkElim___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_mkElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_mkElim___lambda__3), 6, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
x_7 = l_Lean_Meta_DepElim_mkElim___closed__2;
x_8 = 0;
x_9 = l_Lean_Meta_withLocalDecl___rarg(x_7, x_2, x_8, x_6, x_4, x_5);
return x_9;
}
}
lean_object* l_Std_HashSetImp_contains___at_Lean_Meta_DepElim_mkElim___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashSetImp_contains___at_Lean_Meta_DepElim_mkElim___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_Meta_DepElim_mkElim___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_Meta_DepElim_mkElim___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_DepElim_mkElim___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_DepElim_mkElim___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_DepElim_mkElim___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Meta_instantiateMVars(x_6, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l_Lean_Meta_inferType(x_9, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_instantiateMVars(x_12, x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_CollectLevelParams_main___main(x_9, x_1);
x_18 = l_Lean_CollectLevelParams_main___main(x_15, x_17);
x_1 = x_18;
x_2 = x_7;
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("v");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__1;
x_6 = l_List_foldlM___main___at___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___spec__1(x_5, x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__3;
x_10 = l_Lean_CollectLevelParams_State_getUnusedLevelParam(x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__3;
x_14 = l_Lean_CollectLevelParams_State_getUnusedLevelParam(x_11, x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_39__mkElimSort(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_3 == 0)
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_mkSort(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = l_Lean_mkSort(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = l_Lean_Expr_getAppArgs___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_39__mkElimSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Meta_EqnCompiler_DepElim_39__mkElimSort(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_DepElim_mkElimTester___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_Meta_mkForall(x_4, x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_DepElim_mkElim(x_2, x_8, x_3, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElimTester___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_d");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_DepElim_mkElimTester___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_DepElim_mkElimTester___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_DepElim_mkElimTester(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_2);
x_7 = l___private_Lean_Meta_EqnCompiler_DepElim_39__mkElimSort(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_redLength___main___rarg(x_2);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_12 = l_List_toArrayAux___main___rarg(x_2, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_DepElim_mkElimTester___lambda__1), 6, 3);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Lean_Meta_DepElim_mkElimTester___closed__2;
x_15 = l_Lean_Meta_generalizeTelescope___rarg(x_12, x_14, x_13, x_5, x_9);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_DepElim_mkElimTester___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Meta_DepElim_mkElimTester(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_DepElim_40__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_DepElim_Unify_assign___closed__2;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
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
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object*);
lean_object* initialize_Lean_Meta_GeneralizeTelescope(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_MVarRenaming(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_CaseValues(lean_object*);
lean_object* initialize_Lean_Meta_EqnCompiler_CaseArraySizes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_EqnCompiler_DepElim(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_GeneralizeTelescope(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_MVarRenaming(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_CaseValues(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_EqnCompiler_CaseArraySizes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DepElim_Pattern_Inhabited___closed__1 = _init_l_Lean_Meta_DepElim_Pattern_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_Inhabited___closed__1);
l_Lean_Meta_DepElim_Pattern_Inhabited = _init_l_Lean_Meta_DepElim_Pattern_Inhabited();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_Inhabited);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__1 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__1);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__2 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__2);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__3 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__3);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__5 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__5();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__5);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__6 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__6();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__6);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__7 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__7();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__7);
l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__8 = _init_l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__8();
lean_mark_persistent(l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__8);
l_Lean_Meta_DepElim_Alt_Inhabited___closed__1 = _init_l_Lean_Meta_DepElim_Alt_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Alt_Inhabited___closed__1);
l_Lean_Meta_DepElim_Alt_Inhabited = _init_l_Lean_Meta_DepElim_Alt_Inhabited();
lean_mark_persistent(l_Lean_Meta_DepElim_Alt_Inhabited);
l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__1 = _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__1();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__1);
l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__2 = _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__2();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__2);
l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3 = _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__3);
l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__4 = _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__4();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__4);
l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__5 = _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__5();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__5);
l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__6 = _init_l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__6();
lean_mark_persistent(l_List_map___main___at_Lean_Meta_DepElim_Alt_toMessageData___spec__1___closed__6);
l_Lean_Meta_DepElim_Alt_toMessageData___closed__1 = _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Alt_toMessageData___closed__1);
l_Lean_Meta_DepElim_Alt_toMessageData___closed__2 = _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_Alt_toMessageData___closed__2);
l_Lean_Meta_DepElim_Alt_toMessageData___closed__3 = _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_Alt_toMessageData___closed__3);
l_Lean_Meta_DepElim_Alt_toMessageData___closed__4 = _init_l_Lean_Meta_DepElim_Alt_toMessageData___closed__4();
lean_mark_persistent(l_Lean_Meta_DepElim_Alt_toMessageData___closed__4);
l_Lean_Meta_DepElim_Example_toMessageData___main___closed__1 = _init_l_Lean_Meta_DepElim_Example_toMessageData___main___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Example_toMessageData___main___closed__1);
l_Lean_Meta_DepElim_Example_toMessageData___main___closed__2 = _init_l_Lean_Meta_DepElim_Example_toMessageData___main___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_Example_toMessageData___main___closed__2);
l_Lean_Meta_DepElim_Example_toMessageData___main___closed__3 = _init_l_Lean_Meta_DepElim_Example_toMessageData___main___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_Example_toMessageData___main___closed__3);
l_Lean_Meta_DepElim_Problem_Inhabited___closed__1 = _init_l_Lean_Meta_DepElim_Problem_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_Inhabited___closed__1);
l_Lean_Meta_DepElim_Problem_Inhabited = _init_l_Lean_Meta_DepElim_Problem_Inhabited();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_Inhabited);
l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__1 = _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__1);
l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__2 = _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__2);
l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__3 = _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__3);
l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__4 = _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__4);
l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__5 = _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__5);
l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__6 = _init_l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_DepElim_Problem_toMessageData___lambda__1___closed__6);
l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_1__checkNumPatterns___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__4);
l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__5 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__5);
l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__6 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__6);
l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__7 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_2__withAltsAux___main___rarg___closed__7);
l_Lean_Meta_DepElim_Unify_assign___closed__1 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__1);
l_Lean_Meta_DepElim_Unify_assign___closed__2 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__2);
l_Lean_Meta_DepElim_Unify_assign___closed__3 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__3);
l_Lean_Meta_DepElim_Unify_assign___closed__4 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__4();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__4);
l_Lean_Meta_DepElim_Unify_assign___closed__5 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__5();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__5);
l_Lean_Meta_DepElim_Unify_assign___closed__6 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__6();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__6);
l_Lean_Meta_DepElim_Unify_assign___closed__7 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__7();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__7);
l_Lean_Meta_DepElim_Unify_assign___closed__8 = _init_l_Lean_Meta_DepElim_Unify_assign___closed__8();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_assign___closed__8);
l_Lean_Meta_DepElim_Unify_unify___main___closed__1 = _init_l_Lean_Meta_DepElim_Unify_unify___main___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_unify___main___closed__1);
l_Lean_Meta_DepElim_Unify_unify___main___closed__2 = _init_l_Lean_Meta_DepElim_Unify_unify___main___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_unify___main___closed__2);
l_Lean_Meta_DepElim_Unify_unify___main___closed__3 = _init_l_Lean_Meta_DepElim_Unify_unify___main___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_Unify_unify___main___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_24__expandVarIntoCtor_x3f___closed__1);
l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__1 = _init_l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__1();
lean_mark_persistent(l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__1);
l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__2 = _init_l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__2();
lean_mark_persistent(l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__2);
l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__3 = _init_l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__3();
lean_mark_persistent(l_List_filterMapMAux___main___at___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___spec__8___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__4 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__4();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__4);
l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__5 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__5();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_25__processConstructor___closed__5);
l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_28__processValue___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_32__processArrayLit___closed__3);
l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__1 = _init_l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__1();
lean_mark_persistent(l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__1);
l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2 = _init_l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2();
lean_mark_persistent(l_List_map___main___at___private_Lean_Meta_EqnCompiler_DepElim_33__expandNatValuePattern___spec__1___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_34__traceStep___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_35__traceState___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_36__throwNonSupported___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__3);
l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__4 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_37__process___main___closed__4);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__1 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__1);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__2 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__2);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__3 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__3);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__4 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__4);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__5 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__5);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__6 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__6);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__7 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__7);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__8 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__8);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__9 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__9);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__10 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__10);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__11 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__11);
l_Lean_Meta_DepElim_mkElim___lambda__1___closed__12 = _init_l_Lean_Meta_DepElim_mkElim___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__1___closed__12);
l_Lean_Meta_DepElim_mkElim___lambda__2___closed__1 = _init_l_Lean_Meta_DepElim_mkElim___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__2___closed__1);
l_Lean_Meta_DepElim_mkElim___lambda__2___closed__2 = _init_l_Lean_Meta_DepElim_mkElim___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__2___closed__2);
l_Lean_Meta_DepElim_mkElim___lambda__2___closed__3 = _init_l_Lean_Meta_DepElim_mkElim___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___lambda__2___closed__3);
l_Lean_Meta_DepElim_mkElim___closed__1 = _init_l_Lean_Meta_DepElim_mkElim___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___closed__1);
l_Lean_Meta_DepElim_mkElim___closed__2 = _init_l_Lean_Meta_DepElim_mkElim___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElim___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__1);
l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__2);
l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_DepElim_38__getUnusedLevelParam___closed__3);
l_Lean_Meta_DepElim_mkElimTester___closed__1 = _init_l_Lean_Meta_DepElim_mkElimTester___closed__1();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElimTester___closed__1);
l_Lean_Meta_DepElim_mkElimTester___closed__2 = _init_l_Lean_Meta_DepElim_mkElimTester___closed__2();
lean_mark_persistent(l_Lean_Meta_DepElim_mkElimTester___closed__2);
res = l___private_Lean_Meta_EqnCompiler_DepElim_40__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
