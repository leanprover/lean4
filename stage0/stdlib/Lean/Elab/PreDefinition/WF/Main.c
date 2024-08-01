// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.TerminationArgument Lean.Elab.PreDefinition.WF.PackMutual Lean.Elab.PreDefinition.WF.Preprocess Lean.Elab.PreDefinition.WF.Rel Lean.Elab.PreDefinition.WF.Fix Lean.Elab.PreDefinition.WF.Eqns Lean.Elab.PreDefinition.WF.Ite Lean.Elab.PreDefinition.WF.GuessLex
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
static lean_object* l_Lean_Elab_varyingVarNames___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__12;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at_Lean_Elab_getFixedPrefix___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4(size_t, size_t, lean_object*);
extern lean_object* l_Lean_allowUnsafeReducibility;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_wfRecursion___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_wfRecursion___spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__2;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__7;
lean_object* l_Lean_Meta_markAsRecursive(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_wfRecursion___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__13;
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__7;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__3___closed__1;
static lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__2___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__4;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__17;
static lean_object* l_Lean_Elab_varyingVarNames___closed__2;
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___closed__5;
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_wfRecursion___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at_Lean_Elab_getFixedPrefix___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_PreDefinition_filterAttrs(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___lambda__2___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_MatcherApp_inferMatchType___spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___lambda__2___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__5;
static lean_object* l_panic___at_Lean_Elab_varyingVarNames___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at_Lean_Elab_getFixedPrefix___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_iteToDIte___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___lambda__2___closed__5;
lean_object* l_Lean_HashMap_insert___at_Lean_ForEachExpr_visit___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__8___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__7___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__14;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_preprocess___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4___boxed(lean_object**);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__6___closed__1;
lean_object* l_Lean_Meta_iteToDIte___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_withCommonTelescope___rarg___closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Elab_wfRecursion___lambda__3___closed__2;
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at_Lean_Elab_getFixedPrefix___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__15;
static lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__4;
static lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__7___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__9;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__6;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__18;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at_Lean_Elab_Term_withoutMacroStackAtErr___spec__1(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at_Lean_Elab_getFixedPrefix___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope(lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__3;
static lean_object* l_Lean_Elab_wfRecursion___lambda__8___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__5___closed__1;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at_Lean_Elab_getFixedPrefix___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_wfRecursion___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__1___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___boxed(lean_object**);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__5;
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__3;
lean_object* l_id___rarg___boxed(lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__1;
static lean_object* l_Lean_Elab_wfRecursion___lambda__5___closed__2;
lean_object* l_List_map___at_Lean_Elab_addAndCompileUnsafe___spec__2(lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
static lean_object* l_Lean_Elab_wfRecursion___lambda__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at_Lean_Elab_getFixedPrefix___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instMonadControlReaderT___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10(lean_object*, lean_object*);
static lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_wfRecursion___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__1;
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___boxed(lean_object**);
static lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__8___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_wfRecursion___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__11;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7(size_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_varyingVarNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_wfRecursion___lambda__1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at_Lean_Elab_getFixedPrefix___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737_(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__8;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_varyingVarNames___closed__6;
lean_object* l_List_map___at_Lean_mkConstWithLevelParams___spec__1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__2___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___closed__1;
lean_object* l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go(lean_object*);
static lean_object* l_Lean_Elab_getFixedPrefix___lambda__2___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__6;
static lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at_Lean_Elab_getFixedPrefix___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlReaderT___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Expr_const___override(x_14, x_2);
x_16 = l_Lean_mkAppN(x_15, x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_ArgsPacker_curryProj(x_3, x_16, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_5, x_18, x_20, x_21, x_20, x_22, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_5);
lean_ctor_set(x_18, 4, x_6);
lean_ctor_set(x_18, 5, x_7);
lean_ctor_set(x_18, 6, x_8);
lean_ctor_set_uint8(x_18, sizeof(void*)*7, x_2);
x_19 = 0;
x_20 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_18, x_19, x_9, x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("wf", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2;
x_3 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_10, x_9);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_8, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_8, x_23);
lean_dec(x_8);
x_25 = lean_nat_dec_lt(x_9, x_7);
lean_inc(x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_27 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___boxed), 13, 4);
lean_closure_set(x_27, 0, x_4);
lean_closure_set(x_27, 1, x_5);
lean_closure_set(x_27, 2, x_2);
lean_closure_set(x_27, 3, x_9);
if (x_25 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_Elab_instInhabitedPreDefinition;
x_123 = l_outOfBounds___rarg(x_122);
x_28 = x_123;
goto block_121;
}
else
{
lean_object* x_124; 
x_124 = lean_array_fget(x_3, x_9);
x_28 = x_124;
goto block_121;
}
block_121:
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_28, sizeof(void*)*7);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 6);
lean_inc(x_35);
lean_dec(x_28);
x_36 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_34);
x_37 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_34, x_26, x_27, x_36, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
x_41 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_40, x_13, x_14, x_15, x_16, x_17, x_18, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
x_46 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(x_29, x_30, x_31, x_32, x_33, x_34, x_38, x_35, x_6, x_45, x_13, x_14, x_15, x_16, x_17, x_18, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
x_8 = x_24;
x_9 = x_56;
x_12 = x_55;
x_19 = x_54;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
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
x_62 = !lean_is_exclusive(x_41);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_63 = lean_ctor_get(x_41, 1);
x_64 = lean_ctor_get(x_41, 0);
lean_dec(x_64);
lean_inc(x_33);
x_65 = l_Lean_MessageData_ofName(x_33);
x_66 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_65);
lean_ctor_set(x_41, 0, x_66);
x_67 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_38);
x_69 = l_Lean_MessageData_ofExpr(x_38);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
x_72 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_40, x_71, x_13, x_14, x_15, x_16, x_17, x_18, x_63);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
x_75 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(x_29, x_30, x_31, x_32, x_33, x_34, x_38, x_35, x_6, x_73, x_13, x_14, x_15, x_16, x_17, x_18, x_74);
lean_dec(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
lean_ctor_set(x_75, 0, x_79);
return x_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_dec(x_75);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_dec(x_75);
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec(x_76);
x_85 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
x_8 = x_24;
x_9 = x_85;
x_12 = x_84;
x_19 = x_83;
goto _start;
}
}
else
{
uint8_t x_87; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_75);
if (x_87 == 0)
{
return x_75;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get(x_75, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_75);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_91 = lean_ctor_get(x_41, 1);
lean_inc(x_91);
lean_dec(x_41);
lean_inc(x_33);
x_92 = l_Lean_MessageData_ofName(x_33);
x_93 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_38);
x_97 = l_Lean_MessageData_ofExpr(x_38);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
x_100 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_40, x_99, x_13, x_14, x_15, x_16, x_17, x_18, x_91);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
x_103 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(x_29, x_30, x_31, x_32, x_33, x_34, x_38, x_35, x_6, x_101, x_13, x_14, x_15, x_16, x_17, x_18, x_102);
lean_dec(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
lean_dec(x_104);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
lean_dec(x_103);
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
x_8 = x_24;
x_9 = x_111;
x_12 = x_110;
x_19 = x_109;
goto _start;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_103, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_103, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_115 = x_103;
} else {
 lean_dec_ref(x_103);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_37);
if (x_117 == 0)
{
return x_37;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_37, 0);
x_119 = lean_ctor_get(x_37, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_37);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_12);
lean_ctor_set(x_125, 1, x_19);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_12);
lean_ctor_set(x_126, 1, x_19);
return x_126;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_12);
lean_inc(x_3);
x_14 = lean_array_to_list(lean_box(0), x_3);
x_15 = l_List_map___at_Lean_Elab_addAndCompileUnsafe___spec__2(x_14);
x_16 = lean_array_get_size(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_box(0);
lean_inc(x_16);
x_20 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(x_1, x_2, x_3, x_4, x_13, x_15, x_16, x_16, x_17, x_16, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Expr_bindingBody_x21(x_6);
lean_dec(x_6);
x_10 = lean_expr_instantiate1(x_9, x_1);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_14 = lean_array_uget(x_3, x_4);
x_24 = l_Lean_Expr_bindingDomain_x21(x_14);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_instInhabitedExpr;
x_28 = l_outOfBounds___rarg(x_27);
x_29 = l_Lean_Expr_bindingDomain_x21(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Meta_isExprDefEq(x_24, x_29, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_bindingName_x21(x_14);
x_34 = l_Lean_Expr_bindingName_x21(x_28);
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_14);
x_36 = 1;
x_15 = x_36;
x_16 = x_32;
goto block_23;
}
else
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_binderInfo(x_14);
lean_dec(x_14);
x_38 = l_Lean_Expr_binderInfo(x_28);
lean_dec(x_28);
x_39 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_37, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_31);
x_40 = 1;
x_15 = x_40;
x_16 = x_32;
goto block_23;
}
else
{
uint8_t x_41; 
x_41 = lean_unbox(x_31);
lean_dec(x_31);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 1;
x_15 = x_42;
x_16 = x_32;
goto block_23;
}
else
{
uint8_t x_43; 
x_43 = 0;
x_15 = x_43;
x_16 = x_32;
goto block_23;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_array_fget(x_1, x_25);
x_49 = l_Lean_Expr_bindingDomain_x21(x_48);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lean_Meta_isExprDefEq(x_24, x_49, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Expr_bindingName_x21(x_14);
x_54 = l_Lean_Expr_bindingName_x21(x_48);
x_55 = lean_name_eq(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_55 == 0)
{
uint8_t x_56; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_14);
x_56 = 1;
x_15 = x_56;
x_16 = x_52;
goto block_23;
}
else
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; 
x_57 = l_Lean_Expr_binderInfo(x_14);
lean_dec(x_14);
x_58 = l_Lean_Expr_binderInfo(x_48);
lean_dec(x_48);
x_59 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_57, x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_51);
x_60 = 1;
x_15 = x_60;
x_16 = x_52;
goto block_23;
}
else
{
uint8_t x_61; 
x_61 = lean_unbox(x_51);
lean_dec(x_51);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = 1;
x_15 = x_62;
x_16 = x_52;
goto block_23;
}
else
{
uint8_t x_63; 
x_63 = 0;
x_15 = x_63;
x_16 = x_52;
goto block_23;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
block_23:
{
if (x_15 == 0)
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_12 = x_16;
goto _start;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_68 = 0;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_12);
return x_70;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_isLambda(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_4);
x_12 = lean_array_push(x_1, x_4);
x_13 = lean_array_size(x_2);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(x_4, x_13, x_14, x_2);
lean_dec(x_4);
x_16 = l_Lean_Elab_withCommonTelescope_go___rarg(x_3, x_12, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_48; uint8_t x_49; 
x_11 = lean_array_get_size(x_3);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_11);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_12 = x_50;
goto block_47;
}
else
{
size_t x_51; size_t x_52; uint8_t x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_11);
x_53 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(x_3, x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_12 = x_54;
goto block_47;
}
else
{
lean_object* x_55; 
lean_dec(x_11);
x_55 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_55;
}
}
block_47:
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_11);
if (x_14 == 0)
{
uint8_t x_33; 
lean_dec(x_11);
x_33 = 1;
x_15 = x_33;
x_16 = x_10;
goto block_32;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(x_3, x_11, x_3, x_34, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = 1;
x_15 = x_40;
x_16 = x_39;
goto block_32;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = 0;
x_15 = x_42;
x_16 = x_41;
goto block_32;
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
block_32:
{
if (x_15 == 0)
{
lean_object* x_17; 
x_17 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_withCommonTelescope_go___rarg___lambda__1), 11, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_1);
if (x_14 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_3);
x_19 = l_Lean_instInhabitedExpr;
x_20 = l_outOfBounds___rarg(x_19);
x_21 = l_Lean_Expr_bindingName_x21(x_20);
x_22 = l_Lean_Expr_binderInfo(x_20);
x_23 = l_Lean_Expr_bindingDomain_x21(x_20);
lean_dec(x_20);
x_24 = 0;
x_25 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(x_21, x_22, x_23, x_18, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_array_fget(x_3, x_13);
lean_dec(x_3);
x_27 = l_Lean_Expr_bindingName_x21(x_26);
x_28 = l_Lean_Expr_binderInfo(x_26);
x_29 = l_Lean_Expr_bindingDomain_x21(x_26);
lean_dec(x_26);
x_30 = 0;
x_31 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(x_27, x_28, x_29, x_18, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withCommonTelescope_go___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_withCommonTelescope___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope___spec__1(x_10, x_11, x_1);
x_13 = l_Lean_Elab_withCommonTelescope___rarg___closed__1;
x_14 = l_Lean_Elab_withCommonTelescope_go___rarg(x_2, x_13, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withCommonTelescope___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_uget(x_4, x_6);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_7, 1);
x_20 = lean_ctor_get(x_7, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_27 = lean_ctor_get(x_19, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_array_fget(x_21, x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_32);
x_33 = lean_ctor_get(x_10, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_10, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_10, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_10, 5);
lean_inc(x_38);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
x_41 = lean_ctor_get_uint8(x_10, sizeof(void*)*6 + 1);
x_42 = 0;
x_43 = 2;
lean_ctor_set_uint8(x_33, 6, x_42);
lean_ctor_set_uint8(x_33, 9, x_43);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_37);
lean_ctor_set(x_44, 5, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_41);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_45 = l_Lean_Meta_isExprDefEq(x_17, x_30, x_44, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_7, 0, x_50);
lean_ctor_set(x_45, 0, x_7);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_7, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_7);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; size_t x_55; size_t x_56; 
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_55 = 1;
x_56 = lean_usize_add(x_6, x_55);
x_6 = x_56;
x_14 = x_54;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_19);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_62 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
x_63 = lean_ctor_get_uint8(x_10, sizeof(void*)*6 + 1);
x_64 = lean_ctor_get_uint8(x_33, 0);
x_65 = lean_ctor_get_uint8(x_33, 1);
x_66 = lean_ctor_get_uint8(x_33, 2);
x_67 = lean_ctor_get_uint8(x_33, 3);
x_68 = lean_ctor_get_uint8(x_33, 4);
x_69 = lean_ctor_get_uint8(x_33, 5);
x_70 = lean_ctor_get_uint8(x_33, 7);
x_71 = lean_ctor_get_uint8(x_33, 8);
x_72 = lean_ctor_get_uint8(x_33, 10);
x_73 = lean_ctor_get_uint8(x_33, 11);
x_74 = lean_ctor_get_uint8(x_33, 12);
lean_dec(x_33);
x_75 = 0;
x_76 = 2;
x_77 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_77, 0, x_64);
lean_ctor_set_uint8(x_77, 1, x_65);
lean_ctor_set_uint8(x_77, 2, x_66);
lean_ctor_set_uint8(x_77, 3, x_67);
lean_ctor_set_uint8(x_77, 4, x_68);
lean_ctor_set_uint8(x_77, 5, x_69);
lean_ctor_set_uint8(x_77, 6, x_75);
lean_ctor_set_uint8(x_77, 7, x_70);
lean_ctor_set_uint8(x_77, 8, x_71);
lean_ctor_set_uint8(x_77, 9, x_76);
lean_ctor_set_uint8(x_77, 10, x_72);
lean_ctor_set_uint8(x_77, 11, x_73);
lean_ctor_set_uint8(x_77, 12, x_74);
x_78 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_34);
lean_ctor_set(x_78, 2, x_35);
lean_ctor_set(x_78, 3, x_36);
lean_ctor_set(x_78, 4, x_37);
lean_ctor_set(x_78, 5, x_38);
lean_ctor_set_uint8(x_78, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_78, sizeof(void*)*6 + 1, x_63);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_79 = l_Lean_Meta_isExprDefEq(x_17, x_30, x_78, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_7, 0, x_84);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_7);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; size_t x_87; size_t x_88; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_87 = 1;
x_88 = lean_usize_add(x_6, x_87);
x_6 = x_88;
x_14 = x_86;
goto _start;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_19);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_19);
x_94 = lean_array_fget(x_21, x_22);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_22, x_95);
lean_dec(x_22);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_21);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_23);
x_98 = lean_ctor_get(x_10, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_10, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_10, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_10, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_10, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_10, 5);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
x_105 = lean_ctor_get_uint8(x_10, sizeof(void*)*6 + 1);
x_106 = lean_ctor_get_uint8(x_98, 0);
x_107 = lean_ctor_get_uint8(x_98, 1);
x_108 = lean_ctor_get_uint8(x_98, 2);
x_109 = lean_ctor_get_uint8(x_98, 3);
x_110 = lean_ctor_get_uint8(x_98, 4);
x_111 = lean_ctor_get_uint8(x_98, 5);
x_112 = lean_ctor_get_uint8(x_98, 7);
x_113 = lean_ctor_get_uint8(x_98, 8);
x_114 = lean_ctor_get_uint8(x_98, 10);
x_115 = lean_ctor_get_uint8(x_98, 11);
x_116 = lean_ctor_get_uint8(x_98, 12);
if (lean_is_exclusive(x_98)) {
 x_117 = x_98;
} else {
 lean_dec_ref(x_98);
 x_117 = lean_box(0);
}
x_118 = 0;
x_119 = 2;
if (lean_is_scalar(x_117)) {
 x_120 = lean_alloc_ctor(0, 0, 13);
} else {
 x_120 = x_117;
}
lean_ctor_set_uint8(x_120, 0, x_106);
lean_ctor_set_uint8(x_120, 1, x_107);
lean_ctor_set_uint8(x_120, 2, x_108);
lean_ctor_set_uint8(x_120, 3, x_109);
lean_ctor_set_uint8(x_120, 4, x_110);
lean_ctor_set_uint8(x_120, 5, x_111);
lean_ctor_set_uint8(x_120, 6, x_118);
lean_ctor_set_uint8(x_120, 7, x_112);
lean_ctor_set_uint8(x_120, 8, x_113);
lean_ctor_set_uint8(x_120, 9, x_119);
lean_ctor_set_uint8(x_120, 10, x_114);
lean_ctor_set_uint8(x_120, 11, x_115);
lean_ctor_set_uint8(x_120, 12, x_116);
x_121 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_99);
lean_ctor_set(x_121, 2, x_100);
lean_ctor_set(x_121, 3, x_101);
lean_ctor_set(x_121, 4, x_102);
lean_ctor_set(x_121, 5, x_103);
lean_ctor_set_uint8(x_121, sizeof(void*)*6, x_104);
lean_ctor_set_uint8(x_121, sizeof(void*)*6 + 1, x_105);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_122 = l_Lean_Meta_isExprDefEq(x_17, x_94, x_121, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_7, 1, x_97);
lean_ctor_set(x_7, 0, x_127);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_7);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
else
{
lean_object* x_129; size_t x_130; size_t x_131; 
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_dec(x_122);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_97);
lean_ctor_set(x_7, 0, x_3);
x_130 = 1;
x_131 = lean_usize_add(x_6, x_130);
x_6 = x_131;
x_14 = x_129;
goto _start;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_97);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_133 = lean_ctor_get(x_122, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_122, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_135 = x_122;
} else {
 lean_dec_ref(x_122);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_7, 1);
lean_inc(x_137);
lean_dec(x_7);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 2);
lean_inc(x_140);
x_141 = lean_nat_dec_lt(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_3);
lean_ctor_set(x_142, 1, x_137);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_14);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 x_144 = x_137;
} else {
 lean_dec_ref(x_137);
 x_144 = lean_box(0);
}
x_145 = lean_array_fget(x_138, x_139);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_add(x_139, x_146);
lean_dec(x_139);
if (lean_is_scalar(x_144)) {
 x_148 = lean_alloc_ctor(0, 3, 0);
} else {
 x_148 = x_144;
}
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_140);
x_149 = lean_ctor_get(x_10, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_10, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_10, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_10, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_10, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_10, 5);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
x_156 = lean_ctor_get_uint8(x_10, sizeof(void*)*6 + 1);
x_157 = lean_ctor_get_uint8(x_149, 0);
x_158 = lean_ctor_get_uint8(x_149, 1);
x_159 = lean_ctor_get_uint8(x_149, 2);
x_160 = lean_ctor_get_uint8(x_149, 3);
x_161 = lean_ctor_get_uint8(x_149, 4);
x_162 = lean_ctor_get_uint8(x_149, 5);
x_163 = lean_ctor_get_uint8(x_149, 7);
x_164 = lean_ctor_get_uint8(x_149, 8);
x_165 = lean_ctor_get_uint8(x_149, 10);
x_166 = lean_ctor_get_uint8(x_149, 11);
x_167 = lean_ctor_get_uint8(x_149, 12);
if (lean_is_exclusive(x_149)) {
 x_168 = x_149;
} else {
 lean_dec_ref(x_149);
 x_168 = lean_box(0);
}
x_169 = 0;
x_170 = 2;
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 0, 13);
} else {
 x_171 = x_168;
}
lean_ctor_set_uint8(x_171, 0, x_157);
lean_ctor_set_uint8(x_171, 1, x_158);
lean_ctor_set_uint8(x_171, 2, x_159);
lean_ctor_set_uint8(x_171, 3, x_160);
lean_ctor_set_uint8(x_171, 4, x_161);
lean_ctor_set_uint8(x_171, 5, x_162);
lean_ctor_set_uint8(x_171, 6, x_169);
lean_ctor_set_uint8(x_171, 7, x_163);
lean_ctor_set_uint8(x_171, 8, x_164);
lean_ctor_set_uint8(x_171, 9, x_170);
lean_ctor_set_uint8(x_171, 10, x_165);
lean_ctor_set_uint8(x_171, 11, x_166);
lean_ctor_set_uint8(x_171, 12, x_167);
x_172 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_150);
lean_ctor_set(x_172, 2, x_151);
lean_ctor_set(x_172, 3, x_152);
lean_ctor_set(x_172, 4, x_153);
lean_ctor_set(x_172, 5, x_154);
lean_ctor_set_uint8(x_172, sizeof(void*)*6, x_155);
lean_ctor_set_uint8(x_172, sizeof(void*)*6 + 1, x_156);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_173 = l_Lean_Meta_isExprDefEq(x_17, x_145, x_172, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_177 = x_173;
} else {
 lean_dec_ref(x_173);
 x_177 = lean_box(0);
}
x_178 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_148);
if (lean_is_scalar(x_177)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_177;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_176);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; size_t x_183; size_t x_184; 
x_181 = lean_ctor_get(x_173, 1);
lean_inc(x_181);
lean_dec(x_173);
lean_inc(x_3);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_3);
lean_ctor_set(x_182, 1, x_148);
x_183 = 1;
x_184 = lean_usize_add(x_6, x_183);
x_6 = x_184;
x_7 = x_182;
x_14 = x_181;
goto _start;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_148);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_186 = lean_ctor_get(x_173, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_173, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_188 = x_173;
} else {
 lean_dec_ref(x_173);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___lambda__1), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___boxed), 13, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at_Lean_Elab_getFixedPrefix___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_1, x_5);
x_15 = l_Lean_Meta_visitLambda_visit___at_Lean_Elab_getFixedPrefix___spec__6(x_2, x_3, x_14, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at_Lean_Elab_getFixedPrefix___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_dec(x_4);
x_17 = lean_expr_instantiate_rev(x_14, x_3);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_18 = lean_apply_9(x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_visitLambda_visit___at_Lean_Elab_getFixedPrefix___spec__6___lambda__1), 13, 4);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_15);
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg(x_13, x_16, x_17, x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_expr_instantiate_rev(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_28 = lean_apply_9(x_2, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at_Lean_Elab_getFixedPrefix___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_withCommonTelescope___rarg___closed__1;
x_13 = l_Lean_Meta_visitLambda_visit___at_Lean_Elab_getFixedPrefix___spec__6(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___lambda__1), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___rarg___boxed), 13, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at_Lean_Elab_getFixedPrefix___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_1, x_5);
x_15 = l_Lean_Meta_visitForall_visit___at_Lean_Elab_getFixedPrefix___spec__9(x_2, x_3, x_14, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at_Lean_Elab_getFixedPrefix___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_dec(x_4);
x_17 = lean_expr_instantiate_rev(x_14, x_3);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_18 = lean_apply_9(x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_visitForall_visit___at_Lean_Elab_getFixedPrefix___spec__9___lambda__1), 13, 4);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_15);
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___rarg(x_13, x_16, x_17, x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_expr_instantiate_rev(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_28 = lean_apply_9(x_2, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at_Lean_Elab_getFixedPrefix___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_withCommonTelescope___rarg___closed__1;
x_13 = l_Lean_Meta_visitForall_visit___at_Lean_Elab_getFixedPrefix___spec__9(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___lambda__1), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___rarg___boxed), 13, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at_Lean_Elab_getFixedPrefix___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_1, x_5);
x_15 = l_Lean_Meta_visitLet_visit___at_Lean_Elab_getFixedPrefix___spec__12(x_2, x_3, x_14, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at_Lean_Elab_getFixedPrefix___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 8)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_expr_instantiate_rev(x_14, x_3);
lean_dec(x_14);
x_18 = lean_expr_instantiate_rev(x_15, x_3);
lean_dec(x_15);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_19 = lean_apply_9(x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_21 = lean_apply_9(x_2, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_visitLet_visit___at_Lean_Elab_getFixedPrefix___spec__12___lambda__1), 13, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_16);
x_24 = 0;
x_25 = l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___rarg(x_13, x_17, x_18, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
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
lean_dec(x_1);
x_34 = lean_expr_instantiate_rev(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_35 = lean_apply_9(x_2, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at_Lean_Elab_getFixedPrefix___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_withCommonTelescope___rarg___closed__1;
x_13 = l_Lean_Meta_visitLet_visit___at_Lean_Elab_getFixedPrefix___spec__12(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_HashMap_insert___at_Lean_ForEachExpr_visit___spec__3(x_3, x_1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_5);
x_13 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, x_5);
lean_inc(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_apply_9(x_3, lean_box(0), x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(x_16, x_4);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_33; 
lean_free_object(x_14);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_33 = lean_apply_8(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
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
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_19 = x_37;
x_20 = x_36;
goto block_32;
}
else
{
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_43 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_19 = x_44;
x_20 = x_45;
goto block_32;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
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
lean_dec(x_40);
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
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
case 6:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_dec(x_33);
lean_inc(x_3);
lean_inc(x_2);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4), 12, 3);
lean_closure_set(x_55, 0, x_1);
lean_closure_set(x_55, 1, x_2);
lean_closure_set(x_55, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Meta_visitLambda___at_Lean_Elab_getFixedPrefix___spec__5(x_2, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_19 = x_57;
x_20 = x_58;
goto block_32;
}
else
{
uint8_t x_59; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 7:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_33, 1);
lean_inc(x_63);
lean_dec(x_33);
lean_inc(x_3);
lean_inc(x_2);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4), 12, 3);
lean_closure_set(x_64, 0, x_1);
lean_closure_set(x_64, 1, x_2);
lean_closure_set(x_64, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_65 = l_Lean_Meta_visitForall___at_Lean_Elab_getFixedPrefix___spec__8(x_2, x_64, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_19 = x_66;
x_20 = x_67;
goto block_32;
}
else
{
uint8_t x_68; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
case 8:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_33, 1);
lean_inc(x_72);
lean_dec(x_33);
lean_inc(x_3);
lean_inc(x_2);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4), 12, 3);
lean_closure_set(x_73, 0, x_1);
lean_closure_set(x_73, 1, x_2);
lean_closure_set(x_73, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_Meta_visitLet___at_Lean_Elab_getFixedPrefix___spec__11(x_2, x_73, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_19 = x_75;
x_20 = x_76;
goto block_32;
}
else
{
uint8_t x_77; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_33, 1);
lean_inc(x_81);
lean_dec(x_33);
x_82 = lean_ctor_get(x_4, 1);
lean_inc(x_82);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_83 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_19 = x_84;
x_20 = x_85;
goto block_32;
}
else
{
uint8_t x_86; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 11:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_33, 1);
lean_inc(x_90);
lean_dec(x_33);
x_91 = lean_ctor_get(x_4, 2);
lean_inc(x_91);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_92 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_91, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_19 = x_93;
x_20 = x_94;
goto block_32;
}
else
{
uint8_t x_95; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
default: 
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_33, 1);
lean_inc(x_99);
lean_dec(x_33);
x_100 = lean_box(0);
x_19 = x_100;
x_20 = x_99;
goto block_32;
}
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_33);
if (x_101 == 0)
{
return x_33;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_33, 0);
x_103 = lean_ctor_get(x_33, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_33);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
block_32:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4___lambda__1), 3, 2);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_19);
x_22 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_apply_9(x_3, lean_box(0), x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_105; 
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
x_105 = lean_ctor_get(x_18, 0);
lean_inc(x_105);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_105);
return x_14;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_14, 0);
x_107 = lean_ctor_get(x_14, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_14);
x_108 = l_Lean_HashMapImp_find_x3f___at_Lean_ForEachExpr_visit___spec__1(x_106, x_4);
lean_dec(x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_122; 
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_122 = lean_apply_8(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_107);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_box(0);
x_109 = x_126;
x_110 = x_125;
goto block_121;
}
else
{
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_dec(x_122);
x_128 = lean_ctor_get(x_4, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_4, 1);
lean_inc(x_129);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_130 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_128, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_132 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_129, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_109 = x_133;
x_110 = x_134;
goto block_121;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_137 = x_132;
} else {
 lean_dec_ref(x_132);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_129);
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
x_139 = lean_ctor_get(x_130, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_130, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_141 = x_130;
} else {
 lean_dec_ref(x_130);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
case 6:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_122, 1);
lean_inc(x_143);
lean_dec(x_122);
lean_inc(x_3);
lean_inc(x_2);
x_144 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4), 12, 3);
lean_closure_set(x_144, 0, x_1);
lean_closure_set(x_144, 1, x_2);
lean_closure_set(x_144, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_145 = l_Lean_Meta_visitLambda___at_Lean_Elab_getFixedPrefix___spec__5(x_2, x_144, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_109 = x_146;
x_110 = x_147;
goto block_121;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_150 = x_145;
} else {
 lean_dec_ref(x_145);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
case 7:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_122, 1);
lean_inc(x_152);
lean_dec(x_122);
lean_inc(x_3);
lean_inc(x_2);
x_153 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4), 12, 3);
lean_closure_set(x_153, 0, x_1);
lean_closure_set(x_153, 1, x_2);
lean_closure_set(x_153, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_154 = l_Lean_Meta_visitForall___at_Lean_Elab_getFixedPrefix___spec__8(x_2, x_153, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_109 = x_155;
x_110 = x_156;
goto block_121;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_159 = x_154;
} else {
 lean_dec_ref(x_154);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
case 8:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_122, 1);
lean_inc(x_161);
lean_dec(x_122);
lean_inc(x_3);
lean_inc(x_2);
x_162 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4), 12, 3);
lean_closure_set(x_162, 0, x_1);
lean_closure_set(x_162, 1, x_2);
lean_closure_set(x_162, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_163 = l_Lean_Meta_visitLet___at_Lean_Elab_getFixedPrefix___spec__11(x_2, x_162, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_109 = x_164;
x_110 = x_165;
goto block_121;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_168 = x_163;
} else {
 lean_dec_ref(x_163);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
case 10:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_122, 1);
lean_inc(x_170);
lean_dec(x_122);
x_171 = lean_ctor_get(x_4, 1);
lean_inc(x_171);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_172 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_171, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_109 = x_173;
x_110 = x_174;
goto block_121;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_122, 1);
lean_inc(x_179);
lean_dec(x_122);
x_180 = lean_ctor_get(x_4, 2);
lean_inc(x_180);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_181 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_1, x_2, x_3, x_180, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_109 = x_182;
x_110 = x_183;
goto block_121;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_186 = x_181;
} else {
 lean_dec_ref(x_181);
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
default: 
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_122, 1);
lean_inc(x_188);
lean_dec(x_122);
x_189 = lean_box(0);
x_109 = x_189;
x_110 = x_188;
goto block_121;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
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
x_190 = lean_ctor_get(x_122, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_122, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_192 = x_122;
} else {
 lean_dec_ref(x_122);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
block_121:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_109);
x_111 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4___lambda__1), 3, 2);
lean_closure_set(x_111, 0, x_4);
lean_closure_set(x_111, 1, x_109);
x_112 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_112, 0, x_5);
lean_closure_set(x_112, 1, x_111);
x_113 = lean_apply_9(x_3, lean_box(0), x_112, x_6, x_7, x_8, x_9, x_10, x_11, x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_109);
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_119 = x_113;
} else {
 lean_dec_ref(x_113);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; 
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
x_194 = lean_ctor_get(x_108, 0);
lean_inc(x_194);
lean_dec(x_108);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_107);
return x_195;
}
}
}
else
{
uint8_t x_196; 
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
x_196 = !lean_is_exclusive(x_14);
if (x_196 == 0)
{
return x_14;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_14, 0);
x_198 = lean_ctor_get(x_14, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_14);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_apply_1(x_2, x_9);
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
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_box(0);
x_11 = l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__1;
x_12 = l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__2;
x_13 = lean_st_mk_ref(x_12, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Meta_forEachExpr_x27_visit___at_Lean_Elab_getFixedPrefix___spec__4(x_2, x_10, x_11, x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(x_7, x_1, x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_7, x_16);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_7, x_29, x_31);
x_56 = lean_st_ref_take(x_6, x_14);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_get_size(x_32);
x_60 = lean_nat_dec_le(x_59, x_57);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
x_61 = lean_st_ref_set(x_6, x_57, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_33 = x_62;
goto block_55;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
x_63 = lean_st_ref_set(x_6, x_59, x_58);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_33 = x_64;
goto block_55;
}
block_55:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; 
x_34 = l_Array_toSubarray___rarg(x_2, x_16, x_3);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_size(x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(x_4, x_5, x_35, x_32, x_37, x_21, x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
lean_dec(x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__2;
x_43 = lean_box(0);
x_44 = lean_apply_8(x_42, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_41);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__4;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__5;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlTOfPure___rarg(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__3;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__6;
x_3 = l_instMonadControlTOfMonadControl___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__3;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__7;
x_3 = l_instMonadControlTOfMonadControl___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__6;
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__8;
x_17 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___boxed), 14, 6);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_4);
x_18 = l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3(x_5, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_9);
x_19 = lean_array_uget(x_6, x_8);
x_20 = lean_st_ref_get(x_4, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_22, x_24);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_20);
x_26 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3(x_1, x_2, x_3, x_4, x_19, x_5, x_26, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = 1;
x_38 = lean_usize_add(x_8, x_37);
x_8 = x_38;
x_9 = x_36;
x_16 = x_35;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__2;
lean_ctor_set(x_20, 0, x_44);
return x_20;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_eq(x_45, x_47);
lean_dec(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3(x_1, x_2, x_3, x_4, x_19, x_5, x_49, x_10, x_11, x_12, x_13, x_14, x_15, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = 1;
x_59 = lean_usize_add(x_8, x_58);
x_8 = x_59;
x_9 = x_57;
x_16 = x_56;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_63 = x_50;
} else {
 lean_dec_ref(x_50);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__2;
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_46);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
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
}
static lean_object* _init_l_Lean_Elab_getFixedPrefix___lambda__2___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_array_get_size(x_2);
lean_inc(x_11);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_size(x_3);
x_16 = 0;
x_17 = l_Lean_Elab_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14(x_1, x_2, x_11, x_13, x_17, x_3, x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_getFixedPrefix___lambda__1(x_13, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_13);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_getFixedPrefix___lambda__2___boxed), 10, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_withCommonTelescope___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___rarg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___rarg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_getFixedPrefix___spec__10(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___rarg(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLetDecl___at_Lean_Elab_getFixedPrefix___spec__13(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getFixedPrefix___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_getFixedPrefix___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_nat_dec_eq(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_8);
lean_dec(x_8);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_2);
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = l_Lean_Elab_instInhabitedPreDefinition;
x_18 = l_outOfBounds___rarg(x_17);
x_19 = lean_ctor_get(x_18, 5);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_19, x_16, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_array_fget(x_1, x_14);
x_23 = lean_ctor_get(x_22, 5);
lean_inc(x_23);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_23, x_16, x_24, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_varyingVarNames___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_varyingVarNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Elab_varyingVarNames___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("xs.size = arity\n    ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_varyingVarNames___lambda__2___closed__1;
x_2 = l_Lean_Elab_varyingVarNames___lambda__2___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.WF.Main", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.varyingVarNames", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_varyingVarNames___lambda__2___closed__4;
x_2 = l_Lean_Elab_varyingVarNames___lambda__2___closed__5;
x_3 = lean_unsigned_to_nat(85u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Elab_varyingVarNames___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_eq(x_10, x_1);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = l_Lean_Elab_varyingVarNames___lambda__2___closed__6;
x_13 = l_panic___at_Lean_Elab_varyingVarNames___spec__1(x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_array_get_size(x_3);
x_15 = l_Array_toSubarray___rarg(x_3, x_2, x_14);
x_16 = l_Array_ofSubarray___rarg(x_15);
lean_dec(x_15);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Meta_MatcherApp_inferMatchType___spec__9(x_17, x_18, x_16, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_varyingVarNames___lambda__2___boxed), 9, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
x_13 = 0;
x_14 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_10, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_varyingVarNames___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fixedPrefixSize ≤ arity\n  ", 28, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_varyingVarNames___lambda__2___closed__1;
x_2 = l_Lean_Elab_varyingVarNames___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_varyingVarNames___lambda__2___closed__4;
x_2 = l_Lean_Elab_varyingVarNames___lambda__2___closed__5;
x_3 = lean_unsigned_to_nat(81u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Elab_varyingVarNames___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("well-founded recursion cannot be used, '", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_varyingVarNames___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not take any (non-fixed) arguments", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_varyingVarNames___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_varyingVarNames___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = l_Lean_Elab_varyingVarNames___closed__1;
x_10 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_dec_le(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_varyingVarNames___closed__4;
x_16 = l_panic___at_Lean_Elab_varyingVarNames___spec__1(x_15, x_3, x_4, x_5, x_6, x_13);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_12, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Elab_varyingVarNames___lambda__3(x_2, x_12, x_1, x_18, x_3, x_4, x_5, x_6, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_MessageData_ofName(x_20);
x_22 = l_Lean_Elab_varyingVarNames___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_varyingVarNames___closed__8;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_25, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_varyingVarNames___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_varyingVarNames___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_varyingVarNames___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_varyingVarNames___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_wfRecursion___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_1, x_4);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_16);
x_3 = x_12;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_wfRecursion___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_wfRecursion___spec__2(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lambda__2), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 5);
x_23 = lean_ctor_get(x_13, 6);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_22, x_24, x_25, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set(x_13, 5, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_2, x_29);
x_31 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_30;
x_3 = x_31;
x_10 = x_28;
goto _start;
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_39 = lean_ctor_get(x_13, 1);
x_40 = lean_ctor_get(x_13, 2);
x_41 = lean_ctor_get(x_13, 3);
x_42 = lean_ctor_get(x_13, 4);
x_43 = lean_ctor_get(x_13, 5);
x_44 = lean_ctor_get(x_13, 6);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_13);
x_45 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1;
x_46 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
x_47 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_43, x_45, x_46, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_39);
lean_ctor_set(x_50, 2, x_40);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_48);
lean_ctor_set(x_50, 6, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*7, x_38);
x_51 = 1;
x_52 = lean_usize_add(x_2, x_51);
x_53 = lean_array_uset(x_15, x_2, x_50);
x_2 = x_52;
x_3 = x_53;
x_10 = x_49;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_57 = x_47;
} else {
 lean_dec_ref(x_47);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Elab_abstractNestedProofs(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_15, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2;
x_2 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__4;
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 4);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_14, x_1, x_2, x_16, x_17);
x_19 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3;
lean_ctor_set(x_11, 4, x_19);
lean_ctor_set(x_11, 0, x_18);
x_20 = lean_st_ref_set(x_8, x_11, x_12);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_6, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_dec(x_26);
x_27 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5;
lean_ctor_set(x_23, 1, x_27);
x_28 = lean_st_ref_set(x_6, x_23, x_24);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 2);
x_37 = lean_ctor_get(x_23, 3);
x_38 = lean_ctor_get(x_23, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_39 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5;
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_38);
x_41 = lean_st_ref_set(x_6, x_40, x_24);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
x_48 = lean_ctor_get(x_11, 2);
x_49 = lean_ctor_get(x_11, 3);
x_50 = lean_ctor_get(x_11, 5);
x_51 = lean_ctor_get(x_11, 6);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_52 = 0;
x_53 = lean_box(0);
x_54 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_46, x_1, x_2, x_52, x_53);
x_55 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3;
x_56 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set(x_56, 2, x_48);
lean_ctor_set(x_56, 3, x_49);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_50);
lean_ctor_set(x_56, 6, x_51);
x_57 = lean_st_ref_set(x_8, x_56, x_12);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_take(x_6, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 4);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
x_67 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5;
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
x_69 = lean_st_ref_set(x_6, x_68, x_61);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reducible", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("semireducible", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__2;
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__4;
x_10 = lean_name_eq(x_6, x_9);
lean_dec(x_6);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7(size_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_23 = lean_ctor_get(x_15, 3);
lean_inc(x_23);
lean_inc(x_23);
x_24 = l_Lean_Meta_markAsRecursive(x_23, x_10, x_11, x_12);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___closed__1;
lean_inc(x_15);
x_27 = lean_array_push(x_26, x_15);
x_28 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Elab_applyAttributesOf(x_27, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_15, 2);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_array_get_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_33);
lean_dec(x_32);
x_36 = 2;
x_37 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5(x_23, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
x_16 = x_39;
x_17 = x_38;
goto block_22;
}
else
{
size_t x_40; uint8_t x_41; 
x_40 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_41 = l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6(x_32, x_1, x_40);
lean_dec(x_32);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = 2;
x_43 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5(x_23, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
x_16 = x_45;
x_17 = x_44;
goto block_22;
}
else
{
lean_object* x_46; 
lean_dec(x_23);
x_46 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
x_16 = x_46;
x_17 = x_30;
goto block_22;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_29, 0);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
x_5 = x_18;
x_12 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_wfRecursion___spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 6);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
x_15 = l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Elab_addAsAxiom(x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_17 = l_Lean_Elab_varyingVarNames(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_16, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_iteToDIte___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_iteToDIte___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 5);
x_23 = lean_ctor_get(x_13, 6);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__1;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__2;
x_26 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_22, x_24, x_25, x_26, x_26, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_13, 5, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_2, x_30);
x_32 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_31;
x_3 = x_32;
x_10 = x_29;
goto _start;
}
else
{
uint8_t x_34; 
lean_free_object(x_13);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_40 = lean_ctor_get(x_13, 1);
x_41 = lean_ctor_get(x_13, 2);
x_42 = lean_ctor_get(x_13, 3);
x_43 = lean_ctor_get(x_13, 4);
x_44 = lean_ctor_get(x_13, 5);
x_45 = lean_ctor_get(x_13, 6);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_38);
lean_dec(x_13);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__1;
x_47 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__2;
x_48 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_44, x_46, x_47, x_48, x_48, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_40);
lean_ctor_set(x_52, 2, x_41);
lean_ctor_set(x_52, 3, x_42);
lean_ctor_set(x_52, 4, x_43);
lean_ctor_set(x_52, 5, x_50);
lean_ctor_set(x_52, 6, x_45);
lean_ctor_set_uint8(x_52, sizeof(void*)*7, x_39);
x_53 = 1;
x_54 = lean_usize_add(x_2, x_53);
x_55 = lean_array_uset(x_15, x_2, x_52);
x_2 = x_54;
x_3 = x_55;
x_10 = x_51;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_59 = x_49;
} else {
 lean_dec_ref(x_49);
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
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("implemented_by", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_wfRecursion___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_wfRecursion___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Elab_wfRecursion___lambda__1___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
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
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_st_ref_get(x_16, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_16);
lean_inc(x_15);
x_22 = l_Lean_Elab_addAsAxiom(x_1, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4(x_2, x_3, x_4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_25 = l_Lean_Elab_WF_mkFix(x_1, x_5, x_6, x_7, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_wfRecursion___lambda__2___closed__1;
x_29 = l_Lean_Elab_wfRecursion___lambda__2___closed__2;
lean_inc(x_16);
lean_inc(x_15);
x_30 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_26, x_28, x_29, x_15, x_16, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_16, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_35);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_unfoldDeclsFrom(x_36, x_31, x_15, x_16, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 6);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_8);
lean_ctor_set(x_47, 4, x_9);
lean_ctor_set(x_47, 5, x_41);
lean_ctor_set(x_47, 6, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*7, x_43);
x_48 = l_Lean_Elab_wfRecursion___lambda__2___closed__3;
x_49 = l_Lean_Elab_PreDefinition_filterAttrs(x_47, x_48);
lean_ctor_set(x_39, 0, x_49);
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 6);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_8);
lean_ctor_set(x_57, 4, x_9);
lean_ctor_set(x_57, 5, x_50);
lean_ctor_set(x_57, 6, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*7, x_53);
x_58 = l_Lean_Elab_wfRecursion___lambda__2___closed__3;
x_59 = l_Lean_Elab_PreDefinition_filterAttrs(x_57, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_39);
if (x_61 == 0)
{
return x_39;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_39, 0);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_39);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_65 = lean_ctor_get(x_30, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_30, 1);
lean_inc(x_66);
lean_dec(x_30);
x_67 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_66);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_72 = lean_ctor_get(x_25, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_dec(x_25);
x_74 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_73);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_79 = lean_ctor_get(x_22, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_22, 1);
lean_inc(x_80);
lean_dec(x_22);
x_81 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_80);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("wfRel: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
x_18 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
x_22 = lean_box(0);
x_23 = l_Lean_Elab_wfRecursion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_7, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_18, 1);
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
lean_inc(x_9);
x_27 = l_Lean_MessageData_ofExpr(x_9);
x_28 = l_Lean_Elab_wfRecursion___lambda__3___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
x_29 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_17, x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_wfRecursion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_7, x_8, x_32, x_10, x_11, x_12, x_13, x_14, x_15, x_33);
lean_dec(x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
lean_inc(x_9);
x_36 = l_Lean_MessageData_ofExpr(x_9);
x_37 = l_Lean_Elab_wfRecursion___lambda__3___closed__2;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_17, x_40, x_10, x_11, x_12, x_13, x_14, x_15, x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Elab_wfRecursion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_7, x_8, x_42, x_10, x_11, x_12, x_13, x_14, x_15, x_43);
lean_dec(x_42);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_Expr_bindingDomain_x21(x_1);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
x_20 = lean_box_usize(x_3);
x_21 = lean_box_usize(x_4);
lean_inc(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lambda__3___boxed), 16, 8);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, x_6);
lean_closure_set(x_22, 5, x_7);
lean_closure_set(x_22, 6, x_19);
lean_closure_set(x_22, 7, x_8);
x_23 = l_Lean_Elab_WF_elabWFRel___rarg(x_5, x_19, x_6, x_7, x_18, x_9, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("wfRecursion: expected unary function type: ", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = l_Lean_Meta_whnfForall(x_9, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_isForall(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = l_Lean_MessageData_ofExpr(x_18);
x_22 = l_Lean_Elab_wfRecursion___lambda__5___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
x_31 = lean_box(0);
x_32 = l_Lean_Elab_wfRecursion___lambda__4(x_18, x_1, x_2, x_3, x_4, x_8, x_5, x_6, x_7, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
lean_dec(x_18);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_12, 4);
lean_dec(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_dec(x_17);
x_18 = l_Lean_Elab_wfRecursion___lambda__6___closed__1;
x_19 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_18);
lean_ctor_set(x_12, 4, x_19);
lean_ctor_set(x_12, 2, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*12, x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(x_3, x_4, x_5, x_6, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_7, 3);
lean_inc(x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_box(x_27);
lean_inc(x_7);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 10, 3);
lean_closure_set(x_29, 0, x_7);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_26);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_wfRecursion___spec__8(x_27, x_29, x_8, x_9, x_5, x_6, x_12, x_13, x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(x_4, x_10, x_3, x_7, x_8, x_9, x_5, x_6, x_12, x_13, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_dec(x_20);
x_38 = lean_ctor_get(x_7, 3);
lean_inc(x_38);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = 0;
x_42 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_7, x_41, x_40, x_41, x_8, x_9, x_5, x_6, x_12, x_13, x_37);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get(x_12, 1);
x_49 = lean_ctor_get(x_12, 3);
x_50 = lean_ctor_get(x_12, 5);
x_51 = lean_ctor_get(x_12, 6);
x_52 = lean_ctor_get(x_12, 7);
x_53 = lean_ctor_get(x_12, 8);
x_54 = lean_ctor_get(x_12, 9);
x_55 = lean_ctor_get(x_12, 10);
x_56 = lean_ctor_get(x_12, 11);
x_57 = lean_ctor_get_uint8(x_12, sizeof(void*)*12 + 1);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_12);
x_58 = l_Lean_Elab_wfRecursion___lambda__6___closed__1;
x_59 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_58);
x_60 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_48);
lean_ctor_set(x_60, 2, x_1);
lean_ctor_set(x_60, 3, x_49);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_60, 5, x_50);
lean_ctor_set(x_60, 6, x_51);
lean_ctor_set(x_60, 7, x_52);
lean_ctor_set(x_60, 8, x_53);
lean_ctor_set(x_60, 9, x_54);
lean_ctor_set(x_60, 10, x_55);
lean_ctor_set(x_60, 11, x_56);
lean_ctor_set_uint8(x_60, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_60, sizeof(void*)*12 + 1, x_57);
lean_inc(x_13);
lean_inc(x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(x_3, x_4, x_5, x_6, x_60, x_13, x_14);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_7, 3);
lean_inc(x_65);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = 0;
x_69 = lean_box(x_68);
lean_inc(x_7);
x_70 = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 10, 3);
lean_closure_set(x_70, 0, x_7);
lean_closure_set(x_70, 1, x_69);
lean_closure_set(x_70, 2, x_67);
lean_inc(x_13);
lean_inc(x_60);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_9);
lean_inc(x_8);
x_71 = l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_wfRecursion___spec__8(x_68, x_70, x_8, x_9, x_5, x_6, x_60, x_13, x_64);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(x_4, x_10, x_3, x_7, x_8, x_9, x_5, x_6, x_60, x_13, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_60);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_78 = lean_ctor_get(x_61, 1);
lean_inc(x_78);
lean_dec(x_61);
x_79 = lean_ctor_get(x_7, 3);
lean_inc(x_79);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = 0;
x_83 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_7, x_82, x_81, x_82, x_8, x_9, x_5, x_6, x_60, x_13, x_78);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_60);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = lean_ctor_get(x_61, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_61, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_86 = x_61;
} else {
 lean_dec_ref(x_61);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_allowUnsafeReducibility;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__7(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_52 = lean_ctor_get(x_12, 2);
lean_inc(x_52);
x_53 = l_Lean_Elab_wfRecursion___lambda__7___closed__1;
x_54 = 1;
x_55 = l_Lean_Option_set___at_Lean_Elab_Term_withoutMacroStackAtErr___spec__1(x_52, x_53, x_54);
x_56 = l_Lean_Elab_wfRecursion___lambda__7___closed__2;
x_57 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_55, x_56);
x_58 = lean_st_ref_get(x_13, x_17);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Kernel_isDiagnosticsEnabled(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
if (x_57 == 0)
{
x_63 = x_54;
goto block_106;
}
else
{
uint8_t x_107; 
x_107 = 0;
x_63 = x_107;
goto block_106;
}
}
else
{
if (x_57 == 0)
{
uint8_t x_108; 
x_108 = 0;
x_63 = x_108;
goto block_106;
}
else
{
x_63 = x_54;
goto block_106;
}
}
block_51:
{
lean_object* x_19; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_19 = l_Lean_Elab_addAndCompilePartialRec(x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_size(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__4(x_21, x_2, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_4, 3);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_23);
x_26 = l_Lean_Elab_WF_registerEqnsInfo(x_23, x_25, x_5, x_6, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_size(x_23);
x_29 = lean_box(0);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7(x_2, x_23, x_28, x_2, x_29, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
lean_dec(x_23);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
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
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_22);
if (x_43 == 0)
{
return x_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
block_106:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_st_ref_take(x_13, x_60);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 4);
lean_dec(x_69);
x_70 = l_Lean_Kernel_enableDiag(x_68, x_57);
x_71 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3;
lean_ctor_set(x_65, 4, x_71);
lean_ctor_set(x_65, 0, x_70);
x_72 = lean_st_ref_set(x_13, x_65, x_66);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_16);
x_75 = l_Lean_Elab_wfRecursion___lambda__6(x_55, x_57, x_16, x_5, x_10, x_11, x_4, x_8, x_9, x_6, x_74, x_12, x_13, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_18 = x_76;
goto block_51;
}
else
{
uint8_t x_77; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
x_83 = lean_ctor_get(x_65, 2);
x_84 = lean_ctor_get(x_65, 3);
x_85 = lean_ctor_get(x_65, 5);
x_86 = lean_ctor_get(x_65, 6);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_65);
x_87 = l_Lean_Kernel_enableDiag(x_81, x_57);
x_88 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3;
x_89 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_84);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_85);
lean_ctor_set(x_89, 6, x_86);
x_90 = lean_st_ref_set(x_13, x_89, x_66);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_16);
x_93 = l_Lean_Elab_wfRecursion___lambda__6(x_55, x_57, x_16, x_5, x_10, x_11, x_4, x_8, x_9, x_6, x_92, x_12, x_13, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_18 = x_94;
goto block_51;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
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
lean_object* x_99; lean_object* x_100; 
x_99 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_16);
x_100 = l_Lean_Elab_wfRecursion___lambda__6(x_55, x_57, x_16, x_5, x_10, x_11, x_4, x_8, x_9, x_6, x_99, x_12, x_13, x_60);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_18 = x_101;
goto block_51;
}
else
{
uint8_t x_102; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = !lean_is_exclusive(x_100);
if (x_102 == 0)
{
return x_100;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_100, 0);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_100);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_15);
if (x_109 == 0)
{
return x_15;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_15, 0);
x_111 = lean_ctor_get(x_15, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_15);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(">> ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___lambda__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" :=\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___lambda__8___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_inc(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_box_usize(x_3);
x_18 = lean_box_usize(x_4);
lean_inc(x_15);
lean_inc(x_6);
lean_inc(x_5);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lambda__5___boxed), 16, 7);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_5);
lean_closure_set(x_19, 4, x_6);
lean_closure_set(x_19, 5, x_15);
lean_closure_set(x_19, 6, x_7);
x_20 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_15, x_16, x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
x_25 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_wfRecursion___lambda__7(x_3, x_4, x_5, x_22, x_2, x_6, x_29, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_25, 1);
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_22, 3);
lean_inc(x_34);
x_35 = l_Lean_MessageData_ofName(x_34);
x_36 = l_Lean_Elab_wfRecursion___lambda__8___closed__2;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_35);
lean_ctor_set(x_25, 0, x_36);
x_37 = l_Lean_Elab_wfRecursion___lambda__8___closed__4;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_ctor_get(x_22, 5);
lean_inc(x_39);
x_40 = l_Lean_MessageData_ofExpr(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_24, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_wfRecursion___lambda__7(x_3, x_4, x_5, x_22, x_2, x_6, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_46);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_dec(x_25);
x_49 = lean_ctor_get(x_22, 3);
lean_inc(x_49);
x_50 = l_Lean_MessageData_ofName(x_49);
x_51 = l_Lean_Elab_wfRecursion___lambda__8___closed__2;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_wfRecursion___lambda__8___closed__4;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_ctor_get(x_22, 5);
lean_inc(x_55);
x_56 = l_Lean_MessageData_ofExpr(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_24, x_59, x_8, x_9, x_10, x_11, x_12, x_13, x_48);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Elab_wfRecursion___lambda__7(x_3, x_4, x_5, x_22, x_2, x_6, x_61, x_8, x_9, x_10, x_11, x_12, x_13, x_62);
lean_dec(x_61);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_21);
if (x_64 == 0)
{
return x_21;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_21, 0);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_21);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__10(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
lean_inc(x_1);
x_19 = l_Lean_Elab_WF_packMutual(x_1, x_14, x_17, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fixed prefix: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_wfRecursion___closed__1;
x_11 = l_Array_sequenceMap___at_Lean_Elab_wfRecursion___spec__1(x_2, x_10);
x_12 = lean_array_size(x_1);
x_13 = 0;
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(x_12, x_13, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_size(x_15);
x_38 = lean_st_ref_get(x_8, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__9(x_15, x_17, x_13, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_45 = l_Lean_Elab_getFixedPrefix(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
x_50 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_free_object(x_45);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_54 = l_Lean_Elab_wfRecursion___lambda__9(x_47, x_17, x_13, x_15, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_18 = x_55;
x_19 = x_58;
goto block_37;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_15);
lean_dec(x_11);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_50);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_50, 1);
x_68 = lean_ctor_get(x_50, 0);
lean_dec(x_68);
lean_inc(x_47);
x_69 = l___private_Init_Data_Repr_0__Nat_reprFast(x_47);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_MessageData_ofFormat(x_70);
x_72 = l_Lean_Elab_wfRecursion___closed__3;
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_71);
lean_ctor_set(x_50, 0, x_72);
x_73 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_73);
lean_ctor_set(x_45, 0, x_50);
x_74 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_49, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_77 = l_Lean_Elab_wfRecursion___lambda__9(x_47, x_17, x_13, x_15, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_76);
lean_dec(x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_18 = x_78;
x_19 = x_81;
goto block_37;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_15);
lean_dec(x_11);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set_tag(x_84, 1);
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_50, 1);
lean_inc(x_89);
lean_dec(x_50);
lean_inc(x_47);
x_90 = l___private_Init_Data_Repr_0__Nat_reprFast(x_47);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_MessageData_ofFormat(x_91);
x_93 = l_Lean_Elab_wfRecursion___closed__3;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_95);
lean_ctor_set(x_45, 0, x_94);
x_96 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_49, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_89);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_99 = l_Lean_Elab_wfRecursion___lambda__9(x_47, x_17, x_13, x_15, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_98);
lean_dec(x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_18 = x_100;
x_19 = x_103;
goto block_37;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_15);
lean_dec(x_11);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
x_106 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
 lean_ctor_set_tag(x_109, 1);
}
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_45, 0);
x_111 = lean_ctor_get(x_45, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_45);
x_112 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
x_113 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_111);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_117 = l_Lean_Elab_wfRecursion___lambda__9(x_110, x_17, x_13, x_15, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_119);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_18 = x_118;
x_19 = x_121;
goto block_37;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_15);
lean_dec(x_11);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
lean_dec(x_117);
x_124 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_123);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
 lean_ctor_set_tag(x_127, 1);
}
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_128 = lean_ctor_get(x_113, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_129 = x_113;
} else {
 lean_dec_ref(x_113);
 x_129 = lean_box(0);
}
lean_inc(x_110);
x_130 = l___private_Init_Data_Repr_0__Nat_reprFast(x_110);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l_Lean_MessageData_ofFormat(x_131);
x_133 = l_Lean_Elab_wfRecursion___closed__3;
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(7, 2, 0);
} else {
 x_134 = x_129;
 lean_ctor_set_tag(x_134, 7);
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_112, x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_128);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_140 = l_Lean_Elab_wfRecursion___lambda__9(x_110, x_17, x_13, x_15, x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_139);
lean_dec(x_138);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_18 = x_141;
x_19 = x_144;
goto block_37;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_15);
lean_dec(x_11);
x_145 = lean_ctor_get(x_140, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_147 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_146);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_15);
lean_dec(x_11);
x_151 = lean_ctor_get(x_45, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_45, 1);
lean_inc(x_152);
lean_dec(x_45);
x_153 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_152);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_dec(x_155);
lean_ctor_set_tag(x_153, 1);
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_15);
lean_dec(x_11);
x_158 = lean_ctor_get(x_43, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_43, 1);
lean_inc(x_159);
lean_dec(x_43);
x_160 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_160, 0);
lean_dec(x_162);
lean_ctor_set_tag(x_160, 1);
lean_ctor_set(x_160, 0, x_158);
return x_160;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
block_37:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_23);
lean_inc(x_15);
x_24 = l_Lean_Elab_WF_guessLex(x_15, x_23, x_21, x_22, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_wfRecursion___lambda__8(x_23, x_21, x_17, x_13, x_15, x_22, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec(x_11);
x_36 = l_Lean_Elab_wfRecursion___lambda__8(x_34, x_32, x_17, x_13, x_15, x_33, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_36;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_14);
if (x_165 == 0)
{
return x_14;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_14, 0);
x_167 = lean_ctor_get(x_14, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_14);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_wfRecursion___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_wfRecursion___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_wfRecursion___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Lean_Elab_wfRecursion___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__4(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_wfRecursion___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_wfRecursion___spec__8(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__10(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_wfRecursion___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_19 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_20 = l_Lean_Elab_wfRecursion___lambda__2(x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l_Lean_Elab_wfRecursion___lambda__3(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_20 = l_Lean_Elab_wfRecursion___lambda__4(x_1, x_2, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l_Lean_Elab_wfRecursion___lambda__5(x_1, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Lean_Elab_wfRecursion___lambda__6(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_17 = l_Lean_Elab_wfRecursion___lambda__7(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Lean_Elab_wfRecursion___lambda__8(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_wfRecursion___lambda__9(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_wfRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__2;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__3;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__5;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__7;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__8;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PreDefinition", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__9;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WF", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__11;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__13;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__15;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__17;
x_2 = lean_unsigned_to_nat(2737u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
x_3 = 0;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__18;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_TerminationArgument(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Ite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_TerminationArgument(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Rel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Fix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Ite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8);
l_Lean_Elab_withCommonTelescope___rarg___closed__1 = _init_l_Lean_Elab_withCommonTelescope___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_withCommonTelescope___rarg___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1);
l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__1 = _init_l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__1();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__1);
l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__2 = _init_l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__2();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___at_Lean_Elab_getFixedPrefix___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___lambda__3___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__14___closed__2);
l_Lean_Elab_getFixedPrefix___lambda__2___closed__1 = _init_l_Lean_Elab_getFixedPrefix___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_getFixedPrefix___lambda__2___closed__1);
l_panic___at_Lean_Elab_varyingVarNames___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_varyingVarNames___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_varyingVarNames___spec__1___closed__1);
l_Lean_Elab_varyingVarNames___lambda__2___closed__1 = _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___lambda__2___closed__1);
l_Lean_Elab_varyingVarNames___lambda__2___closed__2 = _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___lambda__2___closed__2);
l_Lean_Elab_varyingVarNames___lambda__2___closed__3 = _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___lambda__2___closed__3);
l_Lean_Elab_varyingVarNames___lambda__2___closed__4 = _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___lambda__2___closed__4);
l_Lean_Elab_varyingVarNames___lambda__2___closed__5 = _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___lambda__2___closed__5);
l_Lean_Elab_varyingVarNames___lambda__2___closed__6 = _init_l_Lean_Elab_varyingVarNames___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___lambda__2___closed__6);
l_Lean_Elab_varyingVarNames___closed__1 = _init_l_Lean_Elab_varyingVarNames___closed__1();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__1);
l_Lean_Elab_varyingVarNames___closed__2 = _init_l_Lean_Elab_varyingVarNames___closed__2();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__2);
l_Lean_Elab_varyingVarNames___closed__3 = _init_l_Lean_Elab_varyingVarNames___closed__3();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__3);
l_Lean_Elab_varyingVarNames___closed__4 = _init_l_Lean_Elab_varyingVarNames___closed__4();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__4);
l_Lean_Elab_varyingVarNames___closed__5 = _init_l_Lean_Elab_varyingVarNames___closed__5();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__5);
l_Lean_Elab_varyingVarNames___closed__6 = _init_l_Lean_Elab_varyingVarNames___closed__6();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__6);
l_Lean_Elab_varyingVarNames___closed__7 = _init_l_Lean_Elab_varyingVarNames___closed__7();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__7);
l_Lean_Elab_varyingVarNames___closed__8 = _init_l_Lean_Elab_varyingVarNames___closed__8();
lean_mark_persistent(l_Lean_Elab_varyingVarNames___closed__8);
l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2);
l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__1 = _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__1();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__1);
l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2 = _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__2);
l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3 = _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__3);
l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__4 = _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__4();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__4);
l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5 = _init_l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5();
lean_mark_persistent(l_Lean_setReducibilityStatus___at_Lean_Elab_wfRecursion___spec__5___closed__5);
l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__1 = _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__1);
l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__2 = _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__2();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__2);
l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__3 = _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__3();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__3);
l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__4 = _init_l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__4();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_Lean_Elab_wfRecursion___spec__6___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__7___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__11___closed__2);
l_Lean_Elab_wfRecursion___lambda__1___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__1___closed__1);
l_Lean_Elab_wfRecursion___lambda__1___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__1___closed__2);
l_Lean_Elab_wfRecursion___lambda__2___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__2___closed__1);
l_Lean_Elab_wfRecursion___lambda__2___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__2___closed__2);
l_Lean_Elab_wfRecursion___lambda__2___closed__3 = _init_l_Lean_Elab_wfRecursion___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__2___closed__3);
l_Lean_Elab_wfRecursion___lambda__3___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__3___closed__1);
l_Lean_Elab_wfRecursion___lambda__3___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__3___closed__2);
l_Lean_Elab_wfRecursion___lambda__5___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__5___closed__1);
l_Lean_Elab_wfRecursion___lambda__5___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__5___closed__2);
l_Lean_Elab_wfRecursion___lambda__6___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__6___closed__1);
l_Lean_Elab_wfRecursion___lambda__7___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__7___closed__1);
l_Lean_Elab_wfRecursion___lambda__7___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__7___closed__2);
l_Lean_Elab_wfRecursion___lambda__8___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__8___closed__1);
l_Lean_Elab_wfRecursion___lambda__8___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__8___closed__2);
l_Lean_Elab_wfRecursion___lambda__8___closed__3 = _init_l_Lean_Elab_wfRecursion___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__8___closed__3);
l_Lean_Elab_wfRecursion___lambda__8___closed__4 = _init_l_Lean_Elab_wfRecursion___lambda__8___closed__4();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__8___closed__4);
l_Lean_Elab_wfRecursion___closed__1 = _init_l_Lean_Elab_wfRecursion___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__1);
l_Lean_Elab_wfRecursion___closed__2 = _init_l_Lean_Elab_wfRecursion___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__2);
l_Lean_Elab_wfRecursion___closed__3 = _init_l_Lean_Elab_wfRecursion___closed__3();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__14);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__15 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__15();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__15);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__16 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__16();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__16);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__17 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__17();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__17);
l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__18 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__18();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737____closed__18);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2737_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
