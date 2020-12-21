// Lean compiler output
// Module: Lean.Meta.Match.Match
// Imports: Init Lean.Util.CollectLevelParams Lean.Util.Recognizers Lean.Compiler.ExternAttr Lean.Meta.Check Lean.Meta.Closure Lean.Meta.Tactic.Cases Lean.Meta.GeneralizeTelescope Lean.Meta.Match.Basic Lean.Meta.Match.MVarRenaming Lean.Meta.Match.CaseValues
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2___closed__1;
lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__5;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__4(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__3;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__2(lean_object*);
extern lean_object* l_Lean_Syntax_strLitToAtom___closed__3;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_occurs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__1(lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2;
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone___boxed(lean_object*);
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_MatcherApp_addArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern_match__1(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___boxed(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__4;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1;
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition_match__1(lean_object*);
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_isAltVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1___boxed(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_substCore___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__5(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__2(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__7;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__1(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__4;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__3(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___boxed(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition_match__1(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3;
uint8_t l_Lean_Meta_Match_Unify_occurs(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__4(lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAlt;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__3;
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__2;
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(lean_object*);
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_assign___closed__3;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2;
lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__2;
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__1;
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar___boxed(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar___boxed(lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher_match__1(lean_object*);
lean_object* l_List_map___at_Lean_Meta_Match_mkMatcher___spec__6(lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__3;
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___boxed__const__1;
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_State_fvarSubst___default;
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues_match__1(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_unify_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__3;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_MatcherApp_addArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_6139_(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__8;
lean_object* l_Lean_Meta_Match_generateMatcherCode___boxed(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__5___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(uint8_t, lean_object*);
lean_object* l_Std_mkHashSet___at_Lean_Meta_Match_State_used___default___spec__1(lean_object*);
lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__3(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts(lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2___closed__3;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__2(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_MatcherApp_addArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__3(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern_match__1(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
lean_object* l_Lean_addTrace___at_Lean_Meta_substCore___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_unify_match__1(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__3(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed(lean_object**);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_isCurrVarInductive___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(lean_object*);
extern lean_object* l_Lean_Meta_evalNat_visit___closed__19;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__2(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__6;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__2(lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4;
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1;
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
extern lean_object* l_Lean_Meta_mkArrow___closed__2;
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__4;
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__6;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__2;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__1(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1;
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(uint8_t, lean_object*);
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1;
lean_object* l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2___closed__4;
lean_object* l_Lean_Meta_Match_Unify_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_occurs_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_State_counterExamples___default;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1;
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2;
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__3;
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern_match__1(lean_object*);
lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2;
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(lean_object*);
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__3;
uint8_t l_Lean_Meta_Match_Unify_occurs___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues___spec__1(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_487____closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__3___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__2;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___boxed(lean_object*);
extern lean_object* l_Lean_instToExprUnit___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Std_HashSetImp_moveEntries___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_unify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2___boxed__const__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__2(lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_assign___closed__1;
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_expandIfVar_match__1(lean_object*);
uint8_t l_List_elem___at_Lean_Occurrences_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_mkSimpleThunkType(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__2(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_assign___closed__4;
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__10;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__3;
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_943____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__4;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__2(lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__3;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_isCurrVarInductive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
lean_object* l_Lean_Meta_Match_Unify_assign___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1;
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_instInhabitedHashSet___closed__1;
lean_object* l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_assign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__2;
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1;
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__1;
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(lean_object*);
lean_object* l_List_map___at_Lean_Meta_Match_mkMatcher___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__3___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_match__2___rarg(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___boxed(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_isCurrVarInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__9;
lean_object* l_Lean_Meta_Match_Unify_expandIfVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_assignGoalOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__1(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___boxed(lean_object*);
lean_object* l_Lean_Meta_mkArrayLit___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Match_isCurrVarInductive_match__1(lean_object*);
lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__11;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_MatcherApp_addArg___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_commitWhen___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___closed__1;
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2;
lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___boxed(lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1;
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_assign___closed__5;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition_match__1(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__5;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__2(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1;
lean_object* l_Lean_Meta_Match_withGoalOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_unify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_expandIfVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_occurs___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___closed__5;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__3;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2;
lean_object* l_Lean_Meta_Match_mkMatcher_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_Match_State_used___default___closed__1;
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_State_used___default;
lean_object* l_Lean_Meta_Match_Unify_occurs___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___closed__5;
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1;
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___boxed(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__3(lean_object*);
lean_object* l_Lean_Meta_Match_Unify_assign___closed__6;
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_isCurrVarInductive_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_isCurrVarInductive___closed__1;
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___boxed(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2;
extern lean_object* l_Lean_Meta_Match_instInhabitedProblem;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern_match__1(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_evalNat_match__1___rarg___closed__1;
lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__1(lean_object*);
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159_(lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(uint8_t, lean_object*);
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_isAltVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__4;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern_match__1(lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Unify_expandIfVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition_match__1(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
lean_object* l_Lean_Meta_cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1;
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Match_generateMatcherCode(lean_object*);
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_6 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthAux___rarg(x_7, x_8);
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
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("incorrect number of patterns");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = 0;
x_10 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1(x_8, x_9, x_2);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__3;
x_14 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
x_16 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_16, x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = x_2 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_14, x_2, x_22);
x_2 = x_21;
x_3 = x_23;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkAppN(x_1, x_3);
x_10 = l_Lean_Meta_mkForallFVars(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_List_redLength___rarg(x_10);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
x_13 = l_List_toArrayAux___rarg(x_10, x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = x_13;
x_17 = lean_box_usize(x_15);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1;
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1___boxed), 8, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
x_20 = x_19;
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1___boxed), 8, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_9, x_22, x_4, x_5, x_6, x_7, x_8);
return x_23;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_array_push(x_2, x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_21 = l_List_mapM___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(x_3, x_14, x_15, x_16, x_17, x_18);
if (x_4 == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_mkAppN(x_13, x_5);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
x_27 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(x_10, x_11, x_12, x_26, x_20, x_14, x_15, x_16, x_17, x_23);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_Lean_instToExprUnit___lambda__1___closed__3;
x_35 = l_Lean_mkApp(x_13, x_34);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_8);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
x_38 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(x_10, x_11, x_12, x_37, x_20, x_14, x_15, x_16, x_17, x_33);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Match");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__2;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("minor premise ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_List_reverse___rarg(x_4);
x_12 = lean_apply_7(x_2, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
x_18 = l_List_redLength___rarg(x_16);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_dec(x_18);
lean_inc(x_16);
x_20 = l_List_toArrayAux___rarg(x_16, x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = x_20;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_22, x_23, x_24);
x_26 = x_25;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_26);
lean_inc(x_1);
x_27 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType(x_1, x_26, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Array_isEmpty___rarg(x_26);
if (x_30 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_array_get_size(x_26);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_28);
lean_ctor_set(x_77, 1, x_76);
x_31 = x_77;
goto block_75;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = l_Lean_mkSimpleThunkType(x_28);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_31 = x_80;
goto block_75;
}
block_75:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_List_lengthAux___rarg(x_4, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_35, x_36);
x_38 = l_Lean_Meta_caseValue___closed__2;
x_39 = l_Lean_Name_appendIndexAfter(x_38, x_37);
x_63 = lean_st_ref_get(x_9, x_29);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 3);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = 0;
x_40 = x_68;
x_41 = x_67;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_71 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_70, x_6, x_7, x_8, x_9, x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_72);
lean_dec(x_72);
x_40 = x_74;
x_41 = x_73;
goto block_62;
}
block_62:
{
if (x_40 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_box(x_30);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed), 18, 12);
lean_closure_set(x_43, 0, x_33);
lean_closure_set(x_43, 1, x_5);
lean_closure_set(x_43, 2, x_16);
lean_closure_set(x_43, 3, x_42);
lean_closure_set(x_43, 4, x_26);
lean_closure_set(x_43, 5, x_15);
lean_closure_set(x_43, 6, x_35);
lean_closure_set(x_43, 7, x_17);
lean_closure_set(x_43, 8, x_4);
lean_closure_set(x_43, 9, x_1);
lean_closure_set(x_43, 10, x_2);
lean_closure_set(x_43, 11, x_14);
x_44 = 0;
x_45 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__2___rarg(x_39, x_44, x_32, x_43, x_6, x_7, x_8, x_9, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
lean_inc(x_39);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_39);
x_47 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_32);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_32);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_KernelException_toMessageData___closed__15;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_56 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_55, x_54, x_6, x_7, x_8, x_9, x_41);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(x_30);
x_59 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed), 18, 12);
lean_closure_set(x_59, 0, x_33);
lean_closure_set(x_59, 1, x_5);
lean_closure_set(x_59, 2, x_16);
lean_closure_set(x_59, 3, x_58);
lean_closure_set(x_59, 4, x_26);
lean_closure_set(x_59, 5, x_15);
lean_closure_set(x_59, 6, x_35);
lean_closure_set(x_59, 7, x_17);
lean_closure_set(x_59, 8, x_4);
lean_closure_set(x_59, 9, x_1);
lean_closure_set(x_59, 10, x_2);
lean_closure_set(x_59, 11, x_14);
x_60 = 0;
x_61 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__2___rarg(x_39, x_60, x_32, x_59, x_6, x_7, x_8, x_9, x_57);
return x_61;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_27);
if (x_81 == 0)
{
return x_27;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_27, 0);
x_83 = lean_ctor_get(x_27, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_27);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_5);
return x_20;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(x_1, x_3, x_2, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_assignGoalOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_assignExprMVar___boxed), 7, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Std_mkHashSet___at_Lean_Meta_Match_State_used___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_State_used___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_State_used___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_State_used___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_State_counterExamples___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_isEmpty___rarg(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_3(x_2, x_7, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(lean_object* x_1) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_3(x_2, x_7, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 4);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_apply_5(x_2, x_7, x_8, x_9, x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_apply_1(x_3, x_1);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 4);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 4);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 4);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 4);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_3(x_2, x_7, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 4);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_8, x_7);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_apply_2(x_3, x_11, x_10);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 4);
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
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(x_1, x_6);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 1;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_2(x_4, x_9, x_8);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_2(x_3, x_12, x_11);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_apply_5(x_2, x_15, x_16, x_17, x_18, x_14);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_5, x_1);
return x_20;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition_match__1___rarg), 5, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 4);
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
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(x_1, x_6);
switch (lean_obj_tag(x_7)) {
case 3:
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
case 4:
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
case 5:
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
default: 
{
return x_8;
}
}
}
}
}
}
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_List_isEmpty___rarg(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; uint8_t x_7; 
x_6 = 1;
x_7 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(x_6, x_3);
return x_7;
}
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 2);
x_9 = 1;
x_10 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(x_9, x_8);
return x_10;
}
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_8, x_7);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_apply_2(x_2, x_11, x_10);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 4);
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
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(x_1, x_6);
switch (lean_obj_tag(x_7)) {
case 1:
{
return x_8;
}
case 3:
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(x_1);
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
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(x_7, x_6);
return x_8;
}
}
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_8, x_7);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_apply_3(x_2, x_11, x_12, x_10);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 4);
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
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(x_1, x_6);
switch (lean_obj_tag(x_7)) {
case 1:
{
return x_8;
}
case 4:
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(x_1);
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
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(x_7, x_6);
return x_8;
}
}
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_8, x_7);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_apply_5(x_2, x_11, x_12, x_13, x_14, x_10);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_apply_1(x_4, x_1);
return x_16;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 4);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
switch (lean_obj_tag(x_7)) {
case 0:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
case 2:
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
default: 
{
return x_5;
}
}
}
}
}
}
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = 0;
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(x_7, x_6);
return x_8;
}
}
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Match.Match");
return x_1;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processSkipInaccessible");
return x_1;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(141u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(lean_object* x_1) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
x_12 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = l_Lean_Meta_Match_instInhabitedAlt;
x_14 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_15 = lean_panic_fn(x_13, x_14);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
lean_ctor_set(x_4, 4, x_18);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
lean_ctor_set(x_4, 4, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_16);
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_11, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_11, 0);
lean_dec(x_24);
x_25 = l_Lean_Meta_Match_instInhabitedAlt;
x_26 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_27 = lean_panic_fn(x_25, x_26);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_28 = l_Lean_Meta_Match_instInhabitedAlt;
x_29 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
x_35 = lean_ctor_get(x_4, 2);
x_36 = lean_ctor_get(x_4, 3);
x_37 = lean_ctor_get(x_4, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_38 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_Lean_Meta_Match_instInhabitedAlt;
x_40 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_41 = lean_panic_fn(x_39, x_40);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_41);
return x_1;
}
else
{
lean_object* x_42; 
lean_free_object(x_1);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 3, x_36);
lean_ctor_set(x_45, 4, x_43);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_47 = x_37;
} else {
 lean_dec_ref(x_37);
 x_47 = lean_box(0);
}
x_48 = l_Lean_Meta_Match_instInhabitedAlt;
x_49 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_50 = lean_panic_fn(x_48, x_49);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 4);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
x_60 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
x_61 = l_Lean_Meta_Match_instInhabitedAlt;
x_62 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_63 = lean_panic_fn(x_61, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_58, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_65);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_67 = x_58;
} else {
 lean_dec_ref(x_58);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_59;
}
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_55);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_68, 3, x_57);
lean_ctor_set(x_68, 4, x_66);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_70 = x_58;
} else {
 lean_dec_ref(x_58);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Meta_Match_instInhabitedAlt;
x_72 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_73 = lean_panic_fn(x_71, x_72);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
return x_74;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(137u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_3 = l_Lean_Meta_Match_instInhabitedProblem;
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_7);
lean_ctor_set(x_1, 2, x_10);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_12);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_13);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashSetImp_moveEntries___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(x_3, x_6);
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
lean_object* l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashSetImp_moveEntries___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_nat_dec_eq(x_6, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
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
x_12 = lean_nat_dec_eq(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(x_11, x_2, x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
}
}
lean_object* l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_2, x_9);
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
x_16 = l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(x_12, x_14);
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
x_17 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(x_9, x_2, x_2);
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
x_25 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_2, x_24);
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
x_31 = l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(x_27, x_29);
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
x_33 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(x_24, x_2, x_2);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = 1;
lean_inc(x_6);
x_11 = l_Lean_Meta_admit(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_6, x_12);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_16, 1, x_21);
x_22 = lean_st_ref_set(x_2, x_16, x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_st_ref_set(x_2, x_33, x_17);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
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
x_43 = lean_ctor_get(x_8, 0);
lean_inc(x_43);
lean_dec(x_8);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_inc(x_6);
x_45 = l_Lean_Meta_Match_assignGoalOf(x_1, x_44, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_get(x_6, x_46);
lean_dec(x_6);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_take(x_2, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_43, 1);
lean_inc(x_54);
lean_dec(x_43);
x_55 = l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(x_53, x_54);
lean_ctor_set(x_50, 0, x_55);
x_56 = lean_st_ref_set(x_2, x_50, x_51);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
lean_dec(x_43);
x_66 = l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(x_63, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_st_ref_set(x_2, x_67, x_51);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_43);
lean_dec(x_6);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
return x_45;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_45, 0);
x_75 = lean_ctor_get(x_45, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_45);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_3(x_2, x_7, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_28; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
x_28 = lean_ctor_get(x_10, 4);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
x_13 = x_10;
x_14 = x_7;
goto block_27;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 5)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_10, 4);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
lean_ctor_set(x_28, 0, x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_36 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(x_34, x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_13 = x_37;
x_14 = x_38;
goto block_27;
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_dec(x_28);
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec(x_29);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_10, 4, x_46);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_47 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(x_44, x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_13 = x_48;
x_14 = x_49;
goto block_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_10, 1);
x_56 = lean_ctor_get(x_10, 2);
x_57 = lean_ctor_get(x_10, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_10);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_59 = x_28;
} else {
 lean_dec_ref(x_28);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_29, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_29, 1);
lean_inc(x_61);
lean_dec(x_29);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_55);
lean_ctor_set(x_63, 2, x_56);
lean_ctor_set(x_63, 3, x_57);
lean_ctor_set(x_63, 4, x_62);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_64 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(x_60, x_1, x_63, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_13 = x_65;
x_14 = x_66;
goto block_27;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_69 = x_64;
} else {
 lean_dec_ref(x_64);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_dec(x_29);
lean_dec(x_28);
x_13 = x_10;
x_14 = x_7;
goto block_27;
}
}
block_27:
{
lean_object* x_15; 
x_15 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_12;
}
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
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
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_12;
}
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_4);
lean_ctor_set(x_10, 3, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processAsPattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_3 = lean_unsigned_to_nat(156u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_13);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed), 9, 3);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_7);
lean_closure_set(x_17, 2, x_14);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_18, x_2, x_3, x_4, x_5, x_6);
return x_19;
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_8, x_7);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_apply_2(x_3, x_11, x_10);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processVariable");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(170u);
x_4 = lean_unsigned_to_nat(40u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_28; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
x_28 = lean_ctor_get(x_10, 4);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
x_29 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_30 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2;
x_31 = lean_panic_fn(x_29, x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = lean_apply_5(x_31, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_13 = x_33;
x_14 = x_34;
goto block_27;
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
switch (lean_obj_tag(x_39)) {
case 0:
{
uint8_t x_40; 
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_10, 4);
lean_dec(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_dec(x_28);
lean_ctor_set(x_10, 4, x_42);
x_13 = x_10;
x_14 = x_7;
goto block_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
x_45 = lean_ctor_get(x_10, 2);
x_46 = lean_ctor_get(x_10, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set(x_48, 4, x_47);
x_13 = x_48;
x_14 = x_7;
goto block_27;
}
}
case 1:
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_10, 4);
lean_dec(x_50);
x_51 = lean_ctor_get(x_28, 1);
lean_inc(x_51);
lean_dec(x_28);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
lean_ctor_set(x_10, 4, x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_53 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(x_52, x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_13 = x_54;
x_14 = x_55;
goto block_27;
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_10, 0);
x_61 = lean_ctor_get(x_10, 1);
x_62 = lean_ctor_get(x_10, 2);
x_63 = lean_ctor_get(x_10, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_10);
x_64 = lean_ctor_get(x_28, 1);
lean_inc(x_64);
lean_dec(x_28);
x_65 = lean_ctor_get(x_39, 0);
lean_inc(x_65);
lean_dec(x_39);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_63);
lean_ctor_set(x_66, 4, x_64);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_67 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(x_65, x_1, x_66, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_13 = x_68;
x_14 = x_69;
goto block_27;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
default: 
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_10);
x_74 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_75 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2;
x_76 = lean_panic_fn(x_74, x_75);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_77 = lean_apply_5(x_76, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_13 = x_78;
x_14 = x_79;
goto block_27;
}
else
{
uint8_t x_80; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
block_27:
{
lean_object* x_15; 
x_15 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_12;
}
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
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
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_12;
}
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
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
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(165u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1), 7, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_13);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed), 9, 3);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_14);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_19, x_2, x_3, x_4, x_5, x_6);
return x_20;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_indentExpr(x_1);
x_11 = l___private_Lean_Meta_Tactic_Cases_0__Lean_Meta_throwInductiveTypeExpected___rarg___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_indentExpr(x_8);
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_KernelException_toMessageData___closed__15;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg(x_18, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_6 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_1, x_2, x_5);
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
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_State_fvarSubst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Meta_Match_Unify_isAltVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_1, x_9, x_2);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
lean_object* l_Lean_Meta_Match_Unify_isAltVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_Unify_isAltVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_Match_Unify_expandIfVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_Unify_expandIfVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Unify_expandIfVar_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_Unify_expandIfVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Meta_FVarSubst_apply(x_13, x_1);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Lean_Meta_FVarSubst_apply(x_15, x_1);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
lean_object* l_Lean_Meta_Match_Unify_expandIfVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_Unify_expandIfVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Match_Unify_occurs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_Unify_occurs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Unify_occurs_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Meta_Match_Unify_occurs___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
uint8_t l_Lean_Meta_Match_Unify_occurs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Unify_occurs___lambda__1___boxed), 2, 1);
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
lean_object* l_Lean_Meta_Match_Unify_occurs___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Match_Unify_occurs___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_Match_Unify_occurs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Match_Unify_occurs(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_12);
lean_inc(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_PersistentArray_push___rarg(x_21, x_23);
lean_ctor_set(x_16, 0, x_24);
x_25 = lean_st_ref_set(x_8, x_15, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_12);
lean_inc(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_33, x_35);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
lean_ctor_set(x_15, 3, x_37);
x_38 = lean_st_ref_set(x_8, x_15, x_17);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
x_45 = lean_ctor_get(x_15, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_46 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_48 = x_16;
} else {
 lean_dec_ref(x_16);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_12);
lean_inc(x_10);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_47, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_46);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_st_ref_set(x_8, x_53, x_17);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_checkTraceOption(x_9, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unify");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
x_2 = l_Lean_Meta_Match_Unify_assign___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assign failed variable is not local, ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Unify_assign___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assign occurs check failed, ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Unify_assign___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_Unify_assign(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_27; 
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Lean_Meta_Match_Unify_occurs(x_1, x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Meta_Match_Unify_isAltVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_59 = lean_st_ref_get(x_8, x_31);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get_uint8(x_61, sizeof(void*)*1);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = 0;
x_33 = x_64;
x_34 = x_63;
goto block_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_67 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unbox(x_68);
lean_dec(x_68);
x_33 = x_70;
x_34 = x_69;
goto block_58;
}
block_58:
{
if (x_33 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = 0;
x_36 = lean_box(x_35);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_32);
x_38 = l_Lean_mkFVar(x_1);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Meta_Match_Unify_assign___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_2);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_KernelException_toMessageData___closed__15;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_49 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_48, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = 0;
x_53 = lean_box(x_52);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_71 = lean_ctor_get(x_28, 1);
lean_inc(x_71);
lean_dec(x_28);
x_87 = lean_st_ref_get(x_8, x_71);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 3);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get_uint8(x_89, sizeof(void*)*1);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = 0;
x_72 = x_92;
x_73 = x_91;
goto block_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_95 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unbox(x_96);
lean_dec(x_96);
x_72 = x_98;
x_73 = x_97;
goto block_86;
}
block_86:
{
if (x_72 == 0)
{
x_10 = x_73;
goto block_26;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_inc(x_1);
x_74 = l_Lean_mkFVar(x_1);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_KernelException_toMessageData___closed__15;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_2);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_2);
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
x_83 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_84 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_83, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_10 = x_85;
goto block_26;
}
}
}
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_st_ref_get(x_8, x_9);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 3);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_ctor_get_uint8(x_127, sizeof(void*)*1);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_dec(x_125);
x_130 = 0;
x_99 = x_130;
x_100 = x_129;
goto block_124;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_dec(x_125);
x_132 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_133 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_131);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
x_99 = x_136;
x_100 = x_135;
goto block_124;
}
block_124:
{
if (x_99 == 0)
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_2);
lean_dec(x_1);
x_101 = 0;
x_102 = lean_box(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_104 = l_Lean_mkFVar(x_1);
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_Meta_Match_Unify_assign___closed__6;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_2);
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_KernelException_toMessageData___closed__15;
x_113 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_115 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_114, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_100);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
x_118 = 0;
x_119 = lean_box(x_118);
lean_ctor_set(x_115, 0, x_119);
return x_115;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = 0;
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
}
}
block_26:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_8, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_FVarSubst_insert(x_14, x_1, x_2);
x_17 = lean_st_ref_set(x_4, x_16, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
}
lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_Match_Unify_assign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Match_Unify_assign(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_Match_Unify_unify_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_14 = lean_box_uint64(x_11);
x_15 = lean_box_uint64(x_13);
x_16 = lean_apply_4(x_5, x_10, x_14, x_12, x_15);
return x_16;
}
case 10:
{
lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_4(x_4, x_1, x_17, x_18, x_20);
return x_21;
}
default: 
{
lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_3(x_6, x_22, x_24, x_2);
return x_25;
}
}
}
case 5:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_3(x_7, x_1, x_26, x_28);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_36 = lean_box_uint64(x_32);
x_37 = lean_box_uint64(x_35);
x_38 = lean_apply_6(x_8, x_30, x_31, x_36, x_33, x_34, x_37);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_4(x_4, x_1, x_39, x_40, x_42);
return x_43;
}
default: 
{
lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_44 = lean_apply_2(x_9, x_1, x_2);
return x_44;
}
}
}
case 10:
{
lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_48 = lean_box_uint64(x_47);
x_49 = lean_apply_4(x_3, x_45, x_46, x_48, x_2);
return x_49;
}
default: 
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_9);
lean_dec(x_4);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_52 = lean_box_uint64(x_51);
x_53 = lean_apply_3(x_7, x_1, x_50, x_52);
return x_53;
}
case 10:
{
lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_9);
lean_dec(x_7);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_57 = lean_box_uint64(x_56);
x_58 = lean_apply_4(x_4, x_1, x_54, x_55, x_57);
return x_58;
}
default: 
{
lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_4);
x_59 = lean_apply_2(x_9, x_1, x_2);
return x_59;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Match_Unify_unify_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Unify_unify_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_Unify_unify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_137; lean_object* x_138; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_st_ref_get(x_8, x_9);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 3);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get_uint8(x_153, sizeof(void*)*1);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
lean_dec(x_151);
x_156 = 0;
x_137 = x_156;
x_138 = x_155;
goto block_150;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
lean_dec(x_151);
x_158 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_159 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_158, x_3, x_4, x_5, x_6, x_7, x_8, x_157);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_unbox(x_160);
lean_dec(x_160);
x_137 = x_162;
x_138 = x_161;
goto block_150;
}
block_136:
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_5, x_6, x_7, x_8, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_1);
x_15 = l_Lean_Meta_Match_Unify_expandIfVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Meta_Match_Unify_expandIfVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_expr_eqv(x_1, x_16);
if (x_22 == 0)
{
lean_free_object(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_20;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = lean_expr_eqv(x_2, x_20);
if (x_24 == 0)
{
lean_free_object(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_20;
x_9 = x_21;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_16);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_free_object(x_18);
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = l_Lean_Meta_Match_Unify_assign(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Meta_Match_Unify_assign(x_27, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_28, 0);
lean_dec(x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
case 10:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_2 = x_37;
x_9 = x_21;
goto _start;
}
default: 
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lean_Meta_Match_Unify_assign(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_40;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_18);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_Meta_Match_Unify_assign(x_41, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_42;
}
case 5:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_18);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_47 = l_Lean_Meta_Match_Unify_unify(x_43, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_48);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_1 = x_44;
x_2 = x_46;
x_9 = x_54;
goto _start;
}
}
else
{
uint8_t x_56; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
case 10:
{
lean_object* x_60; 
lean_free_object(x_18);
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
lean_dec(x_2);
x_2 = x_60;
x_9 = x_21;
goto _start;
}
default: 
{
uint8_t x_62; lean_object* x_63; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_62 = 0;
x_63 = lean_box(x_62);
lean_ctor_set(x_18, 0, x_63);
return x_18;
}
}
}
case 10:
{
lean_object* x_64; 
lean_free_object(x_18);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec(x_1);
x_1 = x_64;
x_9 = x_21;
goto _start;
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_66; lean_object* x_67; 
lean_free_object(x_18);
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
lean_dec(x_2);
x_67 = l_Lean_Meta_Match_Unify_assign(x_66, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_67;
}
case 10:
{
lean_object* x_68; 
lean_free_object(x_18);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
lean_dec(x_2);
x_2 = x_68;
x_9 = x_21;
goto _start;
}
default: 
{
uint8_t x_70; lean_object* x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_70 = 0;
x_71 = lean_box(x_70);
lean_ctor_set(x_18, 0, x_71);
return x_18;
}
}
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_18, 0);
x_73 = lean_ctor_get(x_18, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_18);
x_74 = lean_expr_eqv(x_1, x_16);
if (x_74 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_72;
x_9 = x_73;
goto _start;
}
else
{
uint8_t x_76; 
x_76 = lean_expr_eqv(x_2, x_72);
if (x_76 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_72;
x_9 = x_73;
goto _start;
}
else
{
lean_dec(x_72);
lean_dec(x_16);
switch (lean_obj_tag(x_1)) {
case 1:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = l_Lean_Meta_Match_Unify_assign(x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_81);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = l_Lean_Meta_Match_Unify_assign(x_79, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_86 = x_80;
} else {
 lean_dec_ref(x_80);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
case 10:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
lean_dec(x_2);
x_2 = x_88;
x_9 = x_73;
goto _start;
}
default: 
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
lean_dec(x_1);
x_91 = l_Lean_Meta_Match_Unify_assign(x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_91;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
lean_dec(x_2);
x_93 = l_Lean_Meta_Match_Unify_assign(x_92, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_93;
}
case 5:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_dec(x_1);
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_98 = l_Lean_Meta_Match_Unify_unify(x_94, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_1 = x_95;
x_2 = x_97;
x_9 = x_104;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_108 = x_98;
} else {
 lean_dec_ref(x_98);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
case 10:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_2, 1);
lean_inc(x_110);
lean_dec(x_2);
x_2 = x_110;
x_9 = x_73;
goto _start;
}
default: 
{
uint8_t x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_112 = 0;
x_113 = lean_box(x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_73);
return x_114;
}
}
}
case 10:
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_dec(x_1);
x_1 = x_115;
x_9 = x_73;
goto _start;
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
lean_dec(x_2);
x_118 = l_Lean_Meta_Match_Unify_assign(x_117, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_118;
}
case 10:
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_dec(x_2);
x_2 = x_119;
x_9 = x_73;
goto _start;
}
default: 
{
uint8_t x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_121 = 0;
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_73);
return x_123;
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
uint8_t x_124; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_11);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_11, 0);
lean_dec(x_125);
x_126 = 1;
x_127 = lean_box(x_126);
lean_ctor_set(x_11, 0, x_127);
return x_11;
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_11, 1);
lean_inc(x_128);
lean_dec(x_11);
x_129 = 1;
x_130 = lean_box(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_11);
if (x_132 == 0)
{
return x_11;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_11, 0);
x_134 = lean_ctor_get(x_11, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_11);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
block_150:
{
if (x_137 == 0)
{
x_10 = x_138;
goto block_136;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_inc(x_1);
x_139 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_139, 0, x_1);
x_140 = l_Lean_KernelException_toMessageData___closed__15;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Meta_isLevelDefEqAux___closed__5;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_inc(x_2);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_2);
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_140);
x_147 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_148 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_147, x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_138);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_10 = x_149;
goto block_136;
}
}
}
}
lean_object* l_Lean_Meta_Match_Unify_unify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Match_Unify_unify(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_instantiateMVars(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_instantiateMVars(x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_st_ref_get(x_7, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_mk_ref(x_15, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
x_21 = l_Lean_Meta_Match_Unify_unify(x_10, x_13, x_1, x_19, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_7, x_23);
lean_dec(x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_19, x_25);
lean_dec(x_19);
x_27 = lean_unbox(x_22);
lean_dec(x_22);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_9);
if (x_49 == 0)
{
return x_9;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_3(x_2, x_1, x_4, x_6);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
lean_inc(x_4);
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = x_2 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_14, x_2, x_22);
x_2 = x_21;
x_3 = x_23;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_4);
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
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_8, x_1);
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
x_15 = l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_14, x_1);
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
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_1, x_6);
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
x_12 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_5);
x_8 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_1, x_6);
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
x_11 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_9);
x_12 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_1, x_2, x_7);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = 0;
x_13 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_11, x_12, x_2);
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
x_21 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_1, x_2, x_18);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = 0;
x_24 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_22, x_23, x_2);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
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
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = l_Lean_mkAppN(x_1, x_5);
lean_inc(x_3);
x_13 = l_Lean_Meta_Match_Alt_replaceFVarId(x_2, x_12, x_3);
x_14 = lean_array_get_size(x_5);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
lean_inc(x_5);
x_16 = x_5;
x_17 = lean_box_usize(x_15);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2___boxed__const__1;
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1___boxed), 8, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
x_20 = x_19;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = lean_apply_5(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_to_list(lean_box(0), x_22);
x_25 = lean_ctor_get(x_13, 3);
lean_inc(x_25);
x_26 = l_List_append___rarg(x_24, x_25);
x_27 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(x_26, x_6, x_4, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_box(0);
x_40 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_38, x_26, x_39);
x_41 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_38, x_40);
x_42 = lean_ctor_get(x_13, 4);
lean_inc(x_42);
x_43 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_38, x_42);
x_44 = lean_ctor_get(x_13, 2);
lean_inc(x_44);
lean_dec(x_13);
x_45 = l_Lean_Meta_FVarSubst_apply(x_38, x_44);
x_46 = lean_array_to_list(lean_box(0), x_5);
x_47 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_38, x_41, x_46);
lean_dec(x_38);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
lean_dec(x_3);
x_50 = l_List_append___rarg(x_47, x_43);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_41);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_28, 0, x_51);
return x_27;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_28, 0);
lean_inc(x_52);
lean_dec(x_28);
x_53 = lean_box(0);
x_54 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_52, x_26, x_53);
x_55 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_52, x_54);
x_56 = lean_ctor_get(x_13, 4);
lean_inc(x_56);
x_57 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_52, x_56);
x_58 = lean_ctor_get(x_13, 2);
lean_inc(x_58);
lean_dec(x_13);
x_59 = l_Lean_Meta_FVarSubst_apply(x_52, x_58);
x_60 = lean_array_to_list(lean_box(0), x_5);
x_61 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_52, x_55, x_60);
lean_dec(x_52);
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
lean_dec(x_3);
x_64 = l_List_append___rarg(x_61, x_57);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_59);
lean_ctor_set(x_65, 3, x_55);
lean_ctor_set(x_65, 4, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_27, 0, x_66);
return x_27;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_dec(x_27);
x_68 = lean_ctor_get(x_28, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_69 = x_28;
} else {
 lean_dec_ref(x_28);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
x_71 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_68, x_26, x_70);
x_72 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_68, x_71);
x_73 = lean_ctor_get(x_13, 4);
lean_inc(x_73);
x_74 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_68, x_73);
x_75 = lean_ctor_get(x_13, 2);
lean_inc(x_75);
lean_dec(x_13);
x_76 = l_Lean_Meta_FVarSubst_apply(x_68, x_75);
x_77 = lean_array_to_list(lean_box(0), x_5);
x_78 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_68, x_72, x_77);
lean_dec(x_68);
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 1);
lean_inc(x_80);
lean_dec(x_3);
x_81 = l_List_append___rarg(x_78, x_74);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_76);
lean_ctor_set(x_82, 3, x_72);
lean_ctor_set(x_82, 4, x_81);
if (lean_is_scalar(x_69)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_69;
}
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_67);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_27);
if (x_85 == 0)
{
return x_27;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_27, 0);
x_87 = lean_ctor_get(x_27, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_27);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_21);
if (x_89 == 0)
{
return x_21;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_21, 0);
x_91 = lean_ctor_get(x_21, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_21);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_getLocalDecl(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_mkFVar(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_inferType(x_12, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_whnfD___at_Lean_Meta_getLevel___spec__1(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_19 = l_Lean_Meta_getInductiveUniverseAndParams(x_17, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_24 = l_Lean_mkConst(x_2, x_22);
x_25 = l_Lean_mkAppN(x_24, x_23);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_25);
x_26 = l_Lean_Meta_inferType(x_25, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2), 11, 4);
lean_closure_set(x_29, 0, x_25);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_17);
x_30 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__4___rarg(x_27, x_29, x_5, x_6, x_7, x_8, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
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
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
return x_10;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__3___boxed), 9, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_1);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_9, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_whnfD___at_Lean_Meta_getLevel___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Expr_getAppFn(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_15, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 5)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_17);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_16, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
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
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
lean_ctor_set(x_10, 0, x_36);
return x_10;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = l_Lean_Expr_getAppFn(x_37);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 4)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_getConstInfo___at_Lean_Meta_getParamNames___spec__1(x_40, x_2, x_3, x_4, x_5, x_38);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 5)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_54 = x_41;
} else {
 lean_dec_ref(x_41);
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
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_7);
if (x_62 == 0)
{
return x_7;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_7, 0);
x_64 = lean_ctor_get(x_7, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_7);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
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
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*5);
lean_dec(x_19);
x_21 = lean_box(x_20);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*5);
lean_dec(x_23);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_processInaccessibleAsCtor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_apply_3(x_2, x_5, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_processInaccessibleAsCtor_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 3);
x_10 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 3, x_10);
x_11 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_18 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_17);
x_20 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_2, x_3, x_4, x_19, x_6, x_7);
lean_dec(x_19);
return x_20;
}
}
}
lean_object* l_List_map___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(lean_object* x_1) {
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
x_7 = l_List_map___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_5);
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
x_11 = l_List_map___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dependent match elimination failed, inaccessible pattern found");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nconstructor expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_constructorApp_x3f(x_1, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = l_Lean_Meta_Match_Pattern_toMessageData(x_2);
x_17 = l_Lean_indentD(x_16);
x_18 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_3, x_21, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_name_eq(x_28, x_4);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_14);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_25, 3);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_array_get_size(x_26);
x_34 = l_Array_extract___rarg(x_26, x_32, x_33);
x_35 = lean_array_to_list(lean_box(0), x_34);
x_36 = l_List_map___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_35);
x_37 = l_List_append___rarg(x_36, x_5);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_38, 2, x_7);
lean_ctor_set(x_38, 3, x_8);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_14);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_name_eq(x_44, x_4);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_14);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_41, 3);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_array_get_size(x_42);
x_50 = l_Array_extract___rarg(x_42, x_48, x_49);
x_51 = lean_array_to_list(lean_box(0), x_50);
x_52 = l_List_map___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_51);
x_53 = l_List_append___rarg(x_52, x_5);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_6);
lean_ctor_set(x_54, 2, x_7);
lean_ctor_set(x_54, 3, x_8);
lean_ctor_set(x_54, 4, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_14);
return x_56;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Match.processInaccessibleAsCtor");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
x_3 = lean_unsigned_to_nat(308u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
x_2 = l_myMacro____x40_Init_Notation___hyg_11811____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inaccessible in ctor step ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_12 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2;
x_13 = lean_panic_fn(x_11, x_12);
x_14 = lean_apply_5(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_31; lean_object* x_32; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_42 = lean_st_ref_get(x_6, x_17);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = 0;
x_31 = x_47;
x_32 = x_46;
goto block_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_49, x_3, x_4, x_5, x_6, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_31 = x_53;
x_32 = x_52;
goto block_41;
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_whnfD___at_Lean_Meta_getLevel___spec__1), 6, 1);
lean_closure_set(x_26, 0, x_23);
lean_inc(x_21);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___boxed), 14, 8);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_15);
lean_closure_set(x_27, 2, x_18);
lean_closure_set(x_27, 3, x_2);
lean_closure_set(x_27, 4, x_22);
lean_closure_set(x_27, 5, x_19);
lean_closure_set(x_27, 6, x_20);
lean_closure_set(x_27, 7, x_21);
x_28 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_21, x_28, x_3, x_4, x_5, x_6, x_25);
return x_29;
}
block_41:
{
if (x_31 == 0)
{
x_25 = x_32;
goto block_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_23);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_23);
x_34 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__5;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_KernelException_toMessageData___closed__15;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_39 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_38, x_37, x_3, x_4, x_5, x_6, x_32);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_25 = x_40;
goto block_30;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_dec(x_8);
x_55 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_56 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2;
x_57 = lean_panic_fn(x_55, x_56);
x_58 = lean_apply_5(x_57, x_3, x_4, x_5, x_6, x_54);
return x_58;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_2(x_4, x_9, x_8);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_2(x_3, x_12, x_11);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_apply_5(x_2, x_15, x_16, x_17, x_18, x_14);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_5, x_1);
return x_20;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_2(x_4, x_9, x_8);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_apply_2(x_3, x_12, x_11);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_apply_5(x_2, x_15, x_16, x_17, x_18, x_14);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_5, x_1);
return x_20;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__3___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_4);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = l_List_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType), 6, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_box(0);
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
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_3);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_35; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_Expr_fvarId_x21(x_2);
x_10 = l_Array_empty___closed__1;
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_cases___boxed), 9, 4);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1___lambda__1), 9, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_10);
x_15 = lean_st_ref_get(x_6, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_6, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(x_13, x_14, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_18, x_3, x_4, x_5, x_6, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Meta_setMCtx(x_24, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_35, 0, x_51);
return x_35;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_dec(x_35);
x_53 = lean_ctor_get(x_36, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_54 = x_36;
} else {
 lean_dec_ref(x_36);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_35, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_dec(x_35);
x_25 = x_57;
x_26 = x_58;
goto block_34;
}
block_34:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_18, x_3, x_4, x_5, x_6, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Meta_setMCtx(x_24, x_3, x_4, x_5, x_6, x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_25);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_Meta_FVarSubst_apply(x_8, x_5);
x_10 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(x_1, x_6);
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
x_15 = l_Lean_Meta_FVarSubst_apply(x_14, x_11);
x_16 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(lean_object* x_1) {
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
x_6 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(x_5);
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
x_12 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(x_11);
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
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
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
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_to_list(lean_box(0), x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(x_11);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_Match_Example_replaceFVarId(x_8, x_14, x_6);
lean_dec(x_14);
lean_dec(x_8);
x_16 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(x_1, x_2, x_7);
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
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_array_to_list(lean_box(0), x_21);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(x_22);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_Match_Example_replaceFVarId(x_19, x_25, x_17);
lean_dec(x_25);
lean_dec(x_19);
x_27 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(x_1, x_2, x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_Meta_Match_Example_applyFVarSubst(x_8, x_5);
x_10 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(x_1, x_6);
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
x_15 = l_Lean_Meta_Match_Example_applyFVarSubst(x_14, x_11);
x_16 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 4);
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
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_8, x_5);
x_10 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_1, x_6);
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
x_15 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_14, x_11);
x_16 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_1, x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processConstructor");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(353u);
x_4 = lean_unsigned_to_nat(48u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
x_20 = lean_ctor_get(x_10, 4);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
x_21 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_22 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__2;
x_23 = lean_panic_fn(x_21, x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_apply_5(x_23, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_13 = x_25;
x_14 = x_26;
goto block_19;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
switch (lean_obj_tag(x_31)) {
case 0:
{
lean_object* x_32; 
lean_dec(x_31);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_32 = l_Lean_Meta_Match_processInaccessibleAsCtor(x_10, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_13 = x_33;
x_14 = x_34;
goto block_19;
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 1:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_10, 4);
lean_dec(x_40);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec(x_20);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
lean_ctor_set(x_10, 4, x_41);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_43 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(x_10, x_42, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_13 = x_44;
x_14 = x_45;
goto block_19;
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
x_52 = lean_ctor_get(x_10, 2);
x_53 = lean_ctor_get(x_10, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_dec(x_20);
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
lean_dec(x_31);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_54);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_57 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(x_56, x_55, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_13 = x_58;
x_14 = x_59;
goto block_19;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
case 2:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_10, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_20, 1);
lean_inc(x_66);
lean_dec(x_20);
x_67 = lean_ctor_get(x_31, 3);
lean_inc(x_67);
lean_dec(x_31);
x_68 = l_List_append___rarg(x_67, x_66);
lean_ctor_set(x_10, 4, x_68);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_10);
x_13 = x_69;
x_14 = x_8;
goto block_19;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_10, 0);
x_71 = lean_ctor_get(x_10, 1);
x_72 = lean_ctor_get(x_10, 2);
x_73 = lean_ctor_get(x_10, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_10);
x_74 = lean_ctor_get(x_20, 1);
lean_inc(x_74);
lean_dec(x_20);
x_75 = lean_ctor_get(x_31, 3);
lean_inc(x_75);
lean_dec(x_31);
x_76 = l_List_append___rarg(x_75, x_74);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_13 = x_78;
x_14 = x_8;
goto block_19;
}
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_10);
x_79 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_80 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__2;
x_81 = lean_panic_fn(x_79, x_80);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_82 = lean_apply_5(x_81, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_13 = x_83;
x_14 = x_84;
goto block_19;
}
else
{
uint8_t x_85; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
block_19:
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
x_2 = x_11;
x_8 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_is_scalar(x_12)) {
 x_17 = lean_alloc_ctor(1, 2, 0);
} else {
 x_17 = x_12;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_11;
x_3 = x_17;
x_8 = x_14;
goto _start;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_13 = x_6;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_array_uget(x_6, x_5);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_6, x_5, x_16);
x_18 = x_15;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_to_list(lean_box(0), x_21);
lean_inc(x_3);
x_23 = l_List_append___rarg(x_22, x_3);
x_24 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(x_18, x_23);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_inc(x_18);
x_27 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(x_2, x_18, x_26);
x_28 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(x_18, x_27);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_box(0);
x_31 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(x_25, x_29, x_30);
x_32 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_18, x_31);
lean_dec(x_18);
x_33 = l_List_reverse___rarg(x_32);
x_34 = lean_alloc_closure((void*)(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8), 8, 3);
lean_closure_set(x_34, 0, x_25);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_30);
lean_inc(x_20);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed), 9, 3);
lean_closure_set(x_35, 0, x_20);
lean_closure_set(x_35, 1, x_24);
lean_closure_set(x_35, 2, x_28);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_20, x_36, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 1;
x_41 = x_5 + x_40;
x_42 = x_38;
x_43 = lean_array_uset(x_17, x_5, x_42);
x_5 = x_41;
x_6 = x_43;
x_11 = x_39;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(314u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_54; lean_object* x_55; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_st_ref_get(x_5, x_6);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = 0;
x_54 = x_70;
x_55 = x_69;
goto block_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_73 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_72, x_2, x_3, x_4, x_5, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
x_54 = x_76;
x_55 = x_75;
goto block_64;
}
block_53:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_2, x_3, x_4, x_5, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
lean_inc(x_1);
x_18 = l_Lean_Meta_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(x_1, x_16, x_2, x_3, x_4, x_5, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_1, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
lean_ctor_set(x_1, 1, x_17);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_1);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_17);
x_30 = l_Lean_mkOptionalNode___closed__2;
x_31 = lean_array_push(x_30, x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_34 = x_18;
} else {
 lean_dec_ref(x_18);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_17);
lean_ctor_set(x_35, 2, x_14);
lean_ctor_set(x_35, 3, x_15);
x_36 = l_Lean_mkOptionalNode___closed__2;
x_37 = lean_array_push(x_36, x_35);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_ctor_get(x_19, 0);
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = x_40;
x_44 = lean_box_usize(x_42);
x_45 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___boxed__const__1;
x_46 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___boxed), 11, 6);
lean_closure_set(x_46, 0, x_1);
lean_closure_set(x_46, 1, x_16);
lean_closure_set(x_46, 2, x_17);
lean_closure_set(x_46, 3, x_44);
lean_closure_set(x_46, 4, x_45);
lean_closure_set(x_46, 5, x_43);
x_47 = x_46;
x_48 = lean_apply_5(x_47, x_2, x_3, x_4, x_5, x_39);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
block_64:
{
if (x_54 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_st_ref_get(x_5, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_7 = x_57;
goto block_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_59 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__3;
x_60 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_58, x_59, x_2, x_3, x_4, x_5, x_55);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_st_ref_get(x_5, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_7 = x_63;
goto block_53;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_apply_2(x_3, x_9, x_8);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_apply_5(x_2, x_12, x_13, x_14, x_15, x_11);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_4, x_7, x_17);
return x_18;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processNonVariable");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(372u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compile pattern matching, inaccessible pattern or constructor expected");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_12 = x_2;
} else {
 lean_dec_ref(x_2);
 x_12 = lean_box(0);
}
x_20 = lean_ctor_get(x_10, 4);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
x_21 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_22 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2;
x_23 = lean_panic_fn(x_21, x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_apply_5(x_23, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_13 = x_25;
x_14 = x_26;
goto block_19;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
switch (lean_obj_tag(x_31)) {
case 0:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Meta_Match_processInaccessibleAsCtor(x_10, x_33, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_13 = x_35;
x_14 = x_36;
goto block_19;
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
case 2:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
x_44 = lean_ctor_get(x_10, 2);
x_45 = lean_ctor_get(x_10, 3);
x_46 = lean_ctor_get(x_10, 4);
lean_dec(x_46);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_31, 3);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_name_eq(x_48, x_51);
lean_dec(x_51);
lean_dec(x_48);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_49);
lean_dec(x_47);
lean_free_object(x_10);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_53 = lean_box(0);
x_13 = x_53;
x_14 = x_8;
goto block_19;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_List_append___rarg(x_49, x_47);
lean_ctor_set(x_10, 4, x_54);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_10);
x_13 = x_55;
x_14 = x_8;
goto block_19;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
x_58 = lean_ctor_get(x_10, 2);
x_59 = lean_ctor_get(x_10, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_dec(x_20);
x_61 = lean_ctor_get(x_31, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_31, 3);
lean_inc(x_62);
lean_dec(x_31);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_name_eq(x_61, x_64);
lean_dec(x_64);
lean_dec(x_61);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_66 = lean_box(0);
x_13 = x_66;
x_14 = x_8;
goto block_19;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_List_append___rarg(x_62, x_60);
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_57);
lean_ctor_set(x_68, 2, x_58);
lean_ctor_set(x_68, 3, x_59);
lean_ctor_set(x_68, 4, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_13 = x_69;
x_14 = x_8;
goto block_19;
}
}
}
default: 
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_70 = l_Lean_Meta_Match_Pattern_toMessageData(x_31);
x_71 = l_Lean_indentD(x_70);
x_72 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_KernelException_toMessageData___closed__15;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_75, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
block_19:
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
x_2 = x_11;
x_8 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_is_scalar(x_12)) {
 x_17 = lean_alloc_ctor(1, 2, 0);
} else {
 x_17 = x_12;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_11;
x_3 = x_17;
x_8 = x_14;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compile pattern matching, constructor expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
x_15 = l_Lean_Expr_constructorApp_x3f(x_14, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_indentExpr(x_5);
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_KernelException_toMessageData___closed__15;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(x_20, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_reverse___rarg(x_1);
x_26 = lean_box(0);
lean_inc(x_23);
x_27 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2(x_23, x_25, x_26, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_23, 3);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_array_get_size(x_24);
x_32 = l_Array_extract___rarg(x_24, x_30, x_31);
x_33 = lean_array_to_list(lean_box(0), x_32);
x_34 = l_List_append___rarg(x_33, x_2);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_4);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_23, 3);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_array_get_size(x_24);
x_40 = l_Array_extract___rarg(x_24, x_38, x_39);
x_41 = lean_array_to_list(lean_box(0), x_40);
x_42 = l_List_append___rarg(x_41, x_2);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(358u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_whnfD___at_Lean_Meta_getLevel___spec__1), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1), 10, 4);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_12);
lean_closure_set(x_18, 3, x_14);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_19, x_2, x_3, x_4, x_5, x_6);
return x_20;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 4);
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
x_10 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___spec__2(x_1, x_9);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Array_empty___closed__1;
x_4 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_8, x_7);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_apply_2(x_2, x_11, x_10);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_8, x_7);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_apply_2(x_2, x_11, x_10);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(x_5);
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
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(x_10);
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
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(x_1);
x_12 = l_Lean_Expr_fvarId_x21(x_2);
x_13 = lean_array_fget(x_11, x_4);
lean_dec(x_11);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_Match_Example_replaceFVarId(x_12, x_14, x_9);
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(x_1, x_2, x_3, x_4, lean_box(0), x_10);
lean_ctor_set(x_6, 1, x_16);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
lean_inc(x_1);
x_19 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(x_1);
x_20 = l_Lean_Expr_fvarId_x21(x_2);
x_21 = lean_array_fget(x_19, x_4);
lean_dec(x_19);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Meta_Match_Example_replaceFVarId(x_20, x_22, x_17);
lean_dec(x_22);
lean_dec(x_20);
x_24 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(x_1, x_2, x_3, x_4, lean_box(0), x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Meta_Match_Example_applyFVarSubst(x_7, x_5);
x_9 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(x_1, x_6);
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
x_13 = l_Lean_Meta_Match_Example_applyFVarSubst(x_12, x_10);
x_14 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 4);
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
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_4, 2);
x_12 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_11, x_9);
x_13 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_1, x_2, x_3, x_4, lean_box(0), x_10);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_4, 2);
x_17 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_16, x_14);
x_18 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_1, x_2, x_3, x_4, lean_box(0), x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processValue");
return x_1;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
x_3 = lean_unsigned_to_nat(412u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 2);
x_16 = lean_ctor_get(x_10, 3);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_6);
x_18 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_2, x_3, x_4, lean_box(0), x_6, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_10);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
x_19 = l_Lean_Meta_Match_instInhabitedAlt;
x_20 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_21 = lean_panic_fn(x_19, x_20);
lean_ctor_set(x_7, 1, x_18);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; 
lean_free_object(x_7);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
switch (lean_obj_tag(x_22)) {
case 1:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_ctor_set(x_10, 4, x_24);
x_27 = l_Lean_Meta_Match_Alt_replaceFVarId(x_26, x_6, x_10);
lean_ctor_set(x_17, 1, x_18);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
lean_ctor_set(x_10, 4, x_28);
x_30 = l_Lean_Meta_Match_Alt_replaceFVarId(x_29, x_6, x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
return x_31;
}
}
case 3:
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_17, 1);
x_34 = lean_ctor_get(x_17, 0);
lean_dec(x_34);
lean_ctor_set(x_10, 4, x_33);
lean_ctor_set(x_17, 1, x_18);
lean_ctor_set(x_17, 0, x_10);
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
lean_ctor_set(x_10, 4, x_35);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_18);
return x_36;
}
}
default: 
{
uint8_t x_37; 
lean_dec(x_22);
lean_free_object(x_10);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_17, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_17, 0);
lean_dec(x_39);
x_40 = l_Lean_Meta_Match_instInhabitedAlt;
x_41 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_42 = lean_panic_fn(x_40, x_41);
lean_ctor_set(x_17, 1, x_18);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_17);
x_43 = l_Lean_Meta_Match_instInhabitedAlt;
x_44 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_45 = lean_panic_fn(x_43, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_18);
return x_46;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_7, 1);
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
x_50 = lean_ctor_get(x_10, 2);
x_51 = lean_ctor_get(x_10, 3);
x_52 = lean_ctor_get(x_10, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
lean_inc(x_6);
x_53 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_2, x_3, x_4, lean_box(0), x_6, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_6);
x_54 = l_Lean_Meta_Match_instInhabitedAlt;
x_55 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_56 = lean_panic_fn(x_54, x_55);
lean_ctor_set(x_7, 1, x_53);
lean_ctor_set(x_7, 0, x_56);
return x_7;
}
else
{
lean_object* x_57; 
lean_free_object(x_7);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
switch (lean_obj_tag(x_57)) {
case 1:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_49);
lean_ctor_set(x_61, 2, x_50);
lean_ctor_set(x_61, 3, x_51);
lean_ctor_set(x_61, 4, x_58);
x_62 = l_Lean_Meta_Match_Alt_replaceFVarId(x_60, x_6, x_61);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
return x_63;
}
case 3:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_57);
lean_dec(x_6);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_65 = x_52;
} else {
 lean_dec_ref(x_52);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_49);
lean_ctor_set(x_66, 2, x_50);
lean_ctor_set(x_66, 3, x_51);
lean_ctor_set(x_66, 4, x_64);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_53);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_57);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_6);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_68 = x_52;
} else {
 lean_dec_ref(x_52);
 x_68 = lean_box(0);
}
x_69 = l_Lean_Meta_Match_instInhabitedAlt;
x_70 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_71 = lean_panic_fn(x_69, x_70);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_53);
return x_72;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_7, 0);
x_74 = lean_ctor_get(x_7, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_7);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 4);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
lean_inc(x_6);
x_81 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_2, x_3, x_4, lean_box(0), x_6, x_74);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
x_82 = l_Lean_Meta_Match_instInhabitedAlt;
x_83 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_84 = lean_panic_fn(x_82, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
switch (lean_obj_tag(x_86)) {
case 1:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_88 = x_79;
} else {
 lean_dec_ref(x_79);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
if (lean_is_scalar(x_80)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_80;
}
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_76);
lean_ctor_set(x_90, 2, x_77);
lean_ctor_set(x_90, 3, x_78);
lean_ctor_set(x_90, 4, x_87);
x_91 = l_Lean_Meta_Match_Alt_replaceFVarId(x_89, x_6, x_90);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_81);
return x_92;
}
case 3:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_86);
lean_dec(x_6);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_94 = x_79;
} else {
 lean_dec_ref(x_79);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_80;
}
lean_ctor_set(x_95, 0, x_75);
lean_ctor_set(x_95, 1, x_76);
lean_ctor_set(x_95, 2, x_77);
lean_ctor_set(x_95, 3, x_78);
lean_ctor_set(x_95, 4, x_93);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_81);
return x_96;
}
default: 
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_86);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_97 = x_79;
} else {
 lean_dec_ref(x_79);
 x_97 = lean_box(0);
}
x_98 = l_Lean_Meta_Match_instInhabitedAlt;
x_99 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_100 = lean_panic_fn(x_98, x_99);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_81);
return x_101;
}
}
}
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Meta_FVarSubst_apply(x_7, x_5);
x_9 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_1, x_6);
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
x_13 = l_Lean_Meta_FVarSubst_apply(x_12, x_10);
x_14 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_7, x_18);
lean_dec(x_7);
x_20 = lean_array_fget(x_6, x_8);
x_21 = lean_array_get_size(x_4);
x_22 = lean_nat_dec_lt(x_8, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
x_25 = lean_box(0);
x_26 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(x_23, x_25);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_24);
x_30 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_31 = lean_array_push(x_10, x_29);
x_7 = x_19;
x_8 = x_30;
x_9 = lean_box(0);
x_10 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_array_fget(x_4, x_8);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_inc(x_1);
x_36 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(x_1, x_2, x_5, x_8, lean_box(0), x_35);
x_37 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(x_20, x_36);
x_38 = lean_box(0);
x_39 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(x_33, x_34, x_38);
x_40 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_1, x_5, x_8, x_20, lean_box(0), x_39);
x_41 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_5, x_8, x_20, lean_box(0), x_33, x_40);
lean_inc(x_3);
x_42 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_20, x_3);
x_43 = lean_ctor_get(x_20, 0);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_37);
x_45 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_46 = lean_array_push(x_10, x_44);
x_7 = x_19;
x_8 = x_45;
x_9 = lean_box(0);
x_10 = x_46;
goto _start;
}
}
else
{
lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_15);
return x_48;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
x_3 = lean_unsigned_to_nat(391u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_st_ref_get(x_5, x_6);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_7 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_37, x_2, x_3, x_4, x_5, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_7 = x_41;
goto block_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__3;
x_44 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_37, x_43, x_2, x_3, x_4, x_5, x_42);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_7 = x_45;
goto block_30;
}
}
block_30:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_2, x_3, x_4, x_5, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
lean_inc(x_1);
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(x_1);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Lean_Expr_fvarId_x21(x_13);
x_18 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
x_19 = l_Lean_Meta_caseValues(x_16, x_17, x_15, x_18, x_2, x_3, x_4, x_5, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_20);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(x_1, x_13, x_14, x_15, x_20, x_20, x_22, x_24, lean_box(0), x_23, x_2, x_3, x_4, x_5, x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_20);
lean_dec(x_15);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_3(x_2, x_7, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 4);
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
x_11 = l_List_lengthAux___rarg(x_9, x_10);
x_12 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_1, x_11);
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Array_empty___closed__1;
x_4 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_3, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_1(x_4, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop_match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
lean_inc(x_2);
x_13 = l_Lean_Meta_getLocalDecl(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(x_11, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_free_object(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_2);
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
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
x_32 = l_Lean_Expr_fvarId_x21(x_30);
lean_dec(x_30);
lean_inc(x_2);
x_33 = l_Lean_Meta_getLocalDecl(x_32, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(x_31, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_31);
lean_dec(x_2);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_48 = x_33;
} else {
 lean_dec_ref(x_33);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(lean_object* x_1) {
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
x_8 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(x_5);
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
x_13 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_1, x_7);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
x_16 = lean_nat_add(x_15, x_14);
lean_inc(x_4);
x_17 = l_Lean_Name_appendIndexAfter(x_4, x_16);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1___boxed), 12, 6);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_15);
x_19 = 0;
x_20 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__2___rarg(x_17, x_19, x_3, x_18, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_21 = lean_array_to_list(lean_box(0), x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_22 = l_Lean_Meta_mkArrayLit___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__1(x_3, x_21, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = l_Lean_Meta_Match_Alt_replaceFVarId(x_2, x_23, x_1);
lean_inc(x_21);
x_26 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(x_21, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(x_21);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_25, 3);
x_34 = lean_ctor_get(x_25, 4);
x_35 = lean_ctor_get(x_25, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_25, 0);
lean_dec(x_36);
x_37 = l_List_append___rarg(x_28, x_33);
x_38 = l_List_append___rarg(x_29, x_34);
lean_ctor_set(x_25, 4, x_38);
lean_ctor_set(x_25, 3, x_37);
lean_ctor_set(x_25, 1, x_31);
lean_ctor_set(x_25, 0, x_30);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_25, 2);
x_40 = lean_ctor_get(x_25, 3);
x_41 = lean_ctor_get(x_25, 4);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_42 = l_List_append___rarg(x_28, x_40);
x_43 = l_List_append___rarg(x_29, x_41);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_31);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_26, 0, x_44);
return x_26;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_26);
x_47 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(x_21);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_ctor_get(x_25, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_25, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 x_53 = x_25;
} else {
 lean_dec_ref(x_25);
 x_53 = lean_box(0);
}
x_54 = l_List_append___rarg(x_45, x_51);
x_55 = l_List_append___rarg(x_47, x_52);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 5, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set(x_56, 2, x_50);
lean_ctor_set(x_56, 3, x_54);
lean_ctor_set(x_56, 4, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_46);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_26);
if (x_58 == 0)
{
return x_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_26, 0);
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_22);
if (x_62 == 0)
{
return x_22;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_22, 0);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_22);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_LocalDecl_userName(x_5);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(x_1, x_2, x_3, x_11, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___boxed), 6, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1___boxed), 10, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_10, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_8, x_7);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_apply_3(x_2, x_11, x_12, x_10);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_8, x_7);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_apply_3(x_2, x_11, x_12, x_10);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(x_5);
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
x_11 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Meta_FVarSubst_apply(x_7, x_5);
x_9 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(x_1, x_6);
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
x_13 = l_Lean_Meta_FVarSubst_apply(x_12, x_10);
x_14 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(lean_object* x_1) {
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
x_7 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(x_5);
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
x_11 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
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
lean_inc(x_9);
x_10 = lean_array_to_list(lean_box(0), x_9);
x_11 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(x_10);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Match_Example_replaceFVarId(x_8, x_12, x_6);
lean_dec(x_12);
lean_dec(x_8);
x_14 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(x_1, x_2, x_7);
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
lean_inc(x_18);
x_19 = lean_array_to_list(lean_box(0), x_18);
x_20 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_Match_Example_replaceFVarId(x_17, x_21, x_15);
lean_dec(x_21);
lean_dec(x_17);
x_23 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(x_1, x_2, x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Meta_Match_Example_applyFVarSubst(x_7, x_5);
x_9 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(x_1, x_6);
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
x_13 = l_Lean_Meta_Match_Example_applyFVarSubst(x_12, x_10);
x_14 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 4);
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
x_17 = l_List_lengthAux___rarg(x_15, x_16);
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
x_30 = l_List_lengthAux___rarg(x_28, x_29);
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
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_4, 3);
x_12 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_11, x_9);
x_13 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(x_1, x_2, x_3, x_4, lean_box(0), x_10);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_4, 3);
x_17 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_16, x_14);
x_18 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(x_1, x_2, x_3, x_4, lean_box(0), x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processArrayLit");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(469u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_35; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_19 = x_9;
} else {
 lean_dec_ref(x_9);
 x_19 = lean_box(0);
}
x_35 = lean_ctor_get(x_17, 4);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
x_36 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_37 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
x_38 = lean_panic_fn(x_36, x_37);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = lean_apply_5(x_38, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_20 = x_40;
x_21 = x_41;
goto block_34;
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
switch (lean_obj_tag(x_46)) {
case 1:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_17, 0);
x_49 = lean_ctor_get(x_17, 1);
x_50 = lean_ctor_get(x_17, 2);
x_51 = lean_ctor_get(x_17, 3);
x_52 = lean_ctor_get(x_17, 4);
lean_dec(x_52);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_dec(x_35);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
lean_inc(x_2);
x_55 = l_Lean_Meta_FVarSubst_apply(x_8, x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_56 = l_Lean_Meta_getArrayArgType(x_55, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_ctor_set(x_17, 4, x_53);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_59 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(x_17, x_54, x_57, x_7, x_10, x_11, x_12, x_13, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_20 = x_60;
x_21 = x_61;
goto block_34;
}
else
{
uint8_t x_62; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
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
lean_dec(x_54);
lean_dec(x_53);
lean_free_object(x_17);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
return x_56;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_17, 0);
x_71 = lean_ctor_get(x_17, 1);
x_72 = lean_ctor_get(x_17, 2);
x_73 = lean_ctor_get(x_17, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_17);
x_74 = lean_ctor_get(x_35, 1);
lean_inc(x_74);
lean_dec(x_35);
x_75 = lean_ctor_get(x_46, 0);
lean_inc(x_75);
lean_dec(x_46);
lean_inc(x_2);
x_76 = l_Lean_Meta_FVarSubst_apply(x_8, x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_77 = l_Lean_Meta_getArrayArgType(x_76, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_72);
lean_ctor_set(x_80, 3, x_73);
lean_ctor_set(x_80, 4, x_74);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_81 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(x_80, x_75, x_78, x_7, x_10, x_11, x_12, x_13, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_20 = x_82;
x_21 = x_83;
goto block_34;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_88 = lean_ctor_get(x_77, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_90 = x_77;
} else {
 lean_dec_ref(x_77);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
case 4:
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_17);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_17, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_35, 1);
lean_inc(x_94);
lean_dec(x_35);
x_95 = lean_ctor_get(x_46, 1);
lean_inc(x_95);
lean_dec(x_46);
x_96 = l_List_append___rarg(x_95, x_94);
lean_ctor_set(x_17, 4, x_96);
x_20 = x_17;
x_21 = x_14;
goto block_34;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_17, 0);
x_98 = lean_ctor_get(x_17, 1);
x_99 = lean_ctor_get(x_17, 2);
x_100 = lean_ctor_get(x_17, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_17);
x_101 = lean_ctor_get(x_35, 1);
lean_inc(x_101);
lean_dec(x_35);
x_102 = lean_ctor_get(x_46, 1);
lean_inc(x_102);
lean_dec(x_46);
x_103 = l_List_append___rarg(x_102, x_101);
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_103);
x_20 = x_104;
x_21 = x_14;
goto block_34;
}
}
default: 
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_46);
lean_dec(x_35);
lean_dec(x_17);
x_105 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_106 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
x_107 = lean_panic_fn(x_105, x_106);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_108 = lean_apply_5(x_107, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_20 = x_109;
x_21 = x_110;
goto block_34;
}
else
{
uint8_t x_111; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
}
block_34:
{
lean_object* x_22; 
x_22 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(x_1, x_2, x_3, x_4, x_5, lean_box(0), x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_is_scalar(x_19)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_19;
}
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
if (lean_is_scalar(x_19)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_19;
}
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_19);
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
}
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_7, x_18);
lean_dec(x_7);
x_20 = lean_array_fget(x_6, x_8);
x_21 = lean_array_get_size(x_4);
x_22 = lean_nat_dec_lt(x_8, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
x_25 = lean_box(0);
x_26 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(x_23, x_25);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_24);
x_30 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_31 = lean_array_push(x_10, x_29);
x_7 = x_19;
x_8 = x_30;
x_9 = lean_box(0);
x_10 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_33 = l_instInhabitedNat;
x_34 = lean_array_get(x_33, x_4, x_8);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_20, 3);
lean_inc(x_37);
x_38 = lean_array_to_list(lean_box(0), x_36);
x_39 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(x_38);
lean_inc(x_3);
x_40 = l_List_append___rarg(x_39, x_3);
x_41 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(x_20, x_40);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
lean_inc(x_20);
x_44 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(x_2, x_20, x_43);
x_45 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(x_20, x_44);
x_46 = lean_box(0);
x_47 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(x_34, x_42, x_46);
x_48 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(x_1, x_5, x_8, x_20, lean_box(0), x_47);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
x_49 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(x_1, x_2, x_5, x_8, x_20, lean_box(0), x_34, x_37, x_48, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_37);
lean_dec(x_20);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_35);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_45);
x_53 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_54 = lean_array_push(x_10, x_52);
x_7 = x_19;
x_8 = x_53;
x_9 = lean_box(0);
x_10 = x_54;
x_15 = x_51;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_15);
return x_60;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(445u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("array literal step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_st_ref_get(x_5, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_7 = x_36;
goto block_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_39 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_38, x_2, x_3, x_4, x_5, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_7 = x_42;
goto block_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__3;
x_45 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_38, x_44, x_2, x_3, x_4, x_5, x_43);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_7 = x_46;
goto block_31;
}
}
block_31:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_2, x_3, x_4, x_5, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(x_1);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Lean_Expr_fvarId_x21(x_13);
x_18 = l_Lean_Meta_mkArrow___closed__2;
x_19 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
x_20 = l_Lean_Meta_caseArraySizes(x_16, x_17, x_15, x_18, x_19, x_2, x_3, x_4, x_5, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_21);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(x_1, x_13, x_14, x_15, x_21, x_21, x_23, x_25, lean_box(0), x_24, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_21);
lean_dec(x_15);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 9)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = lean_box_uint64(x_10);
x_17 = lean_apply_3(x_3, x_15, x_16, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_3);
x_18 = lean_box_uint64(x_10);
x_19 = lean_apply_2(x_2, x_18, x_9);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_4, x_1);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_apply_1(x_4, x_1);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_apply_1(x_4, x_1);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Meta_evalNat_match__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1;
x_3 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
lean_object* l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
x_11 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 3)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 9)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_4, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = l_Lean_mkNatLit(x_29);
lean_ctor_set(x_12, 0, x_31);
lean_ctor_set(x_10, 1, x_30);
x_32 = l_Lean_Meta_evalNat_visit___closed__19;
x_33 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_10);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_33);
lean_ctor_set(x_4, 4, x_1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_25);
lean_free_object(x_12);
x_35 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
lean_ctor_set(x_10, 0, x_35);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = l_Lean_mkNatLit(x_41);
lean_ctor_set(x_12, 0, x_43);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Meta_evalNat_visit___closed__19;
x_46 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set(x_4, 4, x_1);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_11);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
lean_free_object(x_12);
x_48 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_4, 4, x_49);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_4);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_51 = x_10;
} else {
 lean_dec_ref(x_10);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
lean_dec(x_15);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_eq(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = lean_box(0);
x_58 = l_Lean_mkNatLit(x_56);
lean_ctor_set(x_12, 0, x_58);
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_51;
}
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Meta_evalNat_visit___closed__19;
x_61 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_1, 1, x_50);
lean_ctor_set(x_1, 0, x_61);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_7);
lean_ctor_set(x_62, 2, x_8);
lean_ctor_set(x_62, 3, x_9);
lean_ctor_set(x_62, 4, x_1);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_11);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_52);
lean_free_object(x_12);
x_64 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
if (lean_is_scalar(x_51)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_51;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_50);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_6);
lean_ctor_set(x_66, 1, x_7);
lean_ctor_set(x_66, 2, x_8);
lean_ctor_set(x_66, 3, x_9);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_66);
return x_1;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_15);
lean_free_object(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
x_67 = !lean_is_exclusive(x_10);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_10, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_10, 0);
lean_dec(x_69);
lean_ctor_set(x_10, 1, x_11);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_70; 
lean_dec(x_10);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_11);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
x_71 = !lean_is_exclusive(x_10);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_10, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_10, 0);
lean_dec(x_73);
lean_ctor_set(x_10, 1, x_11);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_74; 
lean_dec(x_10);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_11);
return x_74;
}
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_12, 0);
lean_inc(x_75);
lean_dec(x_12);
if (lean_obj_tag(x_75) == 9)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_77 = x_4;
} else {
 lean_dec_ref(x_4);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_10, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_79 = x_10;
} else {
 lean_dec_ref(x_10);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_eq(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_sub(x_80, x_83);
lean_dec(x_80);
x_85 = lean_box(0);
x_86 = l_Lean_mkNatLit(x_84);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = l_Lean_Meta_evalNat_visit___closed__19;
x_90 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_85);
lean_ctor_set(x_90, 3, x_88);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_90);
if (lean_is_scalar(x_77)) {
 x_91 = lean_alloc_ctor(0, 5, 0);
} else {
 x_91 = x_77;
}
lean_ctor_set(x_91, 0, x_6);
lean_ctor_set(x_91, 1, x_7);
lean_ctor_set(x_91, 2, x_8);
lean_ctor_set(x_91, 3, x_9);
lean_ctor_set(x_91, 4, x_1);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_11);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_80);
x_93 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
if (lean_is_scalar(x_79)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_79;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_95 = lean_alloc_ctor(0, 5, 0);
} else {
 x_95 = x_77;
}
lean_ctor_set(x_95, 0, x_6);
lean_ctor_set(x_95, 1, x_7);
lean_ctor_set(x_95, 2, x_8);
lean_ctor_set(x_95, 3, x_9);
lean_ctor_set(x_95, 4, x_94);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_95);
return x_1;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_76);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_96 = x_10;
} else {
 lean_dec_ref(x_10);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_4);
lean_ctor_set(x_97, 1, x_11);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_75);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_98 = x_10;
} else {
 lean_dec_ref(x_10);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_4);
lean_ctor_set(x_99, 1, x_11);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_1);
x_100 = !lean_is_exclusive(x_10);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_10, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_10, 0);
lean_dec(x_102);
lean_ctor_set(x_10, 1, x_11);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_103; 
lean_dec(x_10);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_4);
lean_ctor_set(x_103, 1, x_11);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_1, 0);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_1);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_104, 4);
lean_inc(x_110);
x_111 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(x_105);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_104);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 3)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_obj_tag(x_114) == 9)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 x_117 = x_104;
} else {
 lean_dec_ref(x_104);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_110, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_119 = x_110;
} else {
 lean_dec_ref(x_110);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_eq(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_sub(x_120, x_123);
lean_dec(x_120);
x_125 = lean_box(0);
x_126 = l_Lean_mkNatLit(x_124);
if (lean_is_scalar(x_115)) {
 x_127 = lean_alloc_ctor(3, 1, 0);
} else {
 x_127 = x_115;
}
lean_ctor_set(x_127, 0, x_126);
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_119;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
x_129 = l_Lean_Meta_evalNat_visit___closed__19;
x_130 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
lean_ctor_set(x_130, 2, x_125);
lean_ctor_set(x_130, 3, x_128);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_118);
if (lean_is_scalar(x_117)) {
 x_132 = lean_alloc_ctor(0, 5, 0);
} else {
 x_132 = x_117;
}
lean_ctor_set(x_132, 0, x_106);
lean_ctor_set(x_132, 1, x_107);
lean_ctor_set(x_132, 2, x_108);
lean_ctor_set(x_132, 3, x_109);
lean_ctor_set(x_132, 4, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_111);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_120);
lean_dec(x_115);
x_134 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
if (lean_is_scalar(x_119)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_119;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_118);
if (lean_is_scalar(x_117)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_117;
}
lean_ctor_set(x_136, 0, x_106);
lean_ctor_set(x_136, 1, x_107);
lean_ctor_set(x_136, 2, x_108);
lean_ctor_set(x_136, 3, x_109);
lean_ctor_set(x_136, 4, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_111);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_138 = x_110;
} else {
 lean_dec_ref(x_110);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_104);
lean_ctor_set(x_139, 1, x_111);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_140 = x_110;
} else {
 lean_dec_ref(x_110);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_104);
lean_ctor_set(x_141, 1, x_111);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_113);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_142 = x_110;
} else {
 lean_dec_ref(x_110);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_104);
lean_ctor_set(x_143, 1, x_111);
return x_143;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(x_3);
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
x_9 = l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_checkTraceOption(x_8, x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 3);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_11);
lean_inc(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Std_PersistentArray_push___rarg(x_20, x_22);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_st_ref_set(x_7, x_14, x_16);
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
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_11);
lean_inc(x_9);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Std_PersistentArray_push___rarg(x_32, x_34);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_31);
lean_ctor_set(x_14, 3, x_36);
x_37 = lean_st_ref_set(x_7, x_14, x_16);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
x_44 = lean_ctor_get(x_14, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_45 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_47 = x_15;
} else {
 lean_dec_ref(x_15);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_11);
lean_inc(x_9);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Std_PersistentArray_push___rarg(x_46, x_49);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(0, 1, 1);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_45);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_44);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_st_ref_set(x_7, x_52, x_16);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__1(x_19, x_2, x_3, x_4, x_5, x_6, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Lean_stringToMessageData(x_1);
x_31 = l_Lean_KernelException_toMessageData___closed__15;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__2(x_19, x_34, x_2, x_3, x_4, x_5, x_6, x_29);
return x_35;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_Match_Problem_toMessageData(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_2, x_12, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_commitWhen___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___lambda__2___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_commitWhen___at_Lean_Meta_tryUnificationHints_tryCandidate___spec__3___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1___boxed), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__2;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compile pattern matching, stuck at");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_indentD(x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_KernelException_toMessageData___closed__15;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Problem_toMessageData), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_Match_isCurrVarInductive_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_isCurrVarInductive_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_isCurrVarInductive_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_isCurrVarInductive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_isCurrVarInductive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_isCurrVarInductive___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_Match_isCurrVarInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Match_isCurrVarInductive___closed__1;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_14, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
}
}
lean_object* l_Lean_Meta_Match_isCurrVarInductive___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Match_isCurrVarInductive___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 == x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_12, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_2 + x_16;
x_2 = x_17;
x_4 = x_14;
x_10 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non variable");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variable");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nat value to constructor");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("as-pattern");
return x_1;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_16 = l_Lean_Meta_Match_isCurrVarInductive(x_2, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_88; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_88 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_2);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_2);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_2);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_17);
x_92 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__1;
x_93 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_92, x_4, x_5, x_6, x_7, x_8, x_18);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_95 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(x_2, x_5, x_6, x_7, x_8, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_96, x_4, x_5, x_6, x_7, x_8, x_97);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
x_103 = lean_unbox(x_17);
lean_dec(x_17);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_2);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_box(0);
x_19 = x_105;
goto block_87;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2;
x_107 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_106, x_4, x_5, x_6, x_7, x_8, x_18);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_109 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_2, x_5, x_6, x_7, x_8, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_110, x_4, x_5, x_6, x_7, x_8, x_111);
return x_112;
}
else
{
uint8_t x_113; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_113 = !lean_is_exclusive(x_109);
if (x_113 == 0)
{
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 0);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_109);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_117; 
x_117 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_2);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_2);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_box(0);
x_19 = x_119;
goto block_87;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2;
x_121 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_120, x_4, x_5, x_6, x_7, x_8, x_18);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_123 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_2, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_124, x_4, x_5, x_6, x_7, x_8, x_125);
return x_126;
}
else
{
uint8_t x_127; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_127 = !lean_is_exclusive(x_123);
if (x_127 == 0)
{
return x_123;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_123, 0);
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_123);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
else
{
lean_object* x_131; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_131 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(x_2, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
x_135 = lean_array_get_size(x_133);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_135);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_138 = lean_box(0);
lean_ctor_set(x_131, 0, x_138);
return x_131;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_135, x_135);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_140 = lean_box(0);
lean_ctor_set(x_131, 0, x_140);
return x_131;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_131);
x_141 = 0;
x_142 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_143 = lean_box(0);
x_144 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_133, x_141, x_142, x_143, x_4, x_5, x_6, x_7, x_8, x_134);
lean_dec(x_133);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_131, 0);
x_146 = lean_ctor_get(x_131, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_131);
x_147 = lean_array_get_size(x_145);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_lt(x_148, x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_147, x_147);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_146);
return x_154;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; 
x_155 = 0;
x_156 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_157 = lean_box(0);
x_158 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_145, x_155, x_156, x_157, x_4, x_5, x_6, x_7, x_8, x_146);
lean_dec(x_145);
return x_158;
}
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_159 = !lean_is_exclusive(x_131);
if (x_159 == 0)
{
return x_131;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_131, 0);
x_161 = lean_ctor_get(x_131, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_131);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_17);
x_163 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__3;
x_164 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_163, x_4, x_5, x_6, x_7, x_8, x_18);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_2);
x_167 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_166, x_4, x_5, x_6, x_7, x_8, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_17);
x_168 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__4;
x_169 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_168, x_4, x_5, x_6, x_7, x_8, x_18);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_171 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(x_2, x_5, x_6, x_7, x_8, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_172, x_4, x_5, x_6, x_7, x_8, x_173);
return x_174;
}
else
{
uint8_t x_175; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_175 = !lean_is_exclusive(x_171);
if (x_175 == 0)
{
return x_171;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_171, 0);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_171);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_17);
x_179 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(x_2, x_4, x_5, x_6, x_7, x_8, x_18);
return x_179;
}
block_87:
{
uint8_t x_20; 
lean_dec(x_19);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_2);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_2);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(x_2, x_5, x_6, x_7, x_8, x_18);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(x_2, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_array_get_size(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_box(0);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_27, x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_box(0);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_23);
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_35 = lean_box(0);
x_36 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_25, x_33, x_34, x_35, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_25);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_array_get_size(x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_39, x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_37, x_47, x_48, x_49, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_37);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
return x_23;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(x_2, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_array_get_size(x_57);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_62 = lean_box(0);
lean_ctor_set(x_55, 0, x_62);
return x_55;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_59, x_59);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_64 = lean_box(0);
lean_ctor_set(x_55, 0, x_64);
return x_55;
}
else
{
size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_55);
x_65 = 0;
x_66 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_67 = lean_box(0);
x_68 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_57, x_65, x_66, x_67, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_57);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_55, 0);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_55);
x_71 = lean_array_get_size(x_69);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_71, x_71);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
return x_78;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_81 = lean_box(0);
x_82 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_69, x_79, x_80, x_81, x_4, x_5, x_6, x_7, x_8, x_70);
lean_dec(x_69);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_83 = !lean_is_exclusive(x_55);
if (x_83 == 0)
{
return x_55;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_55, 0);
x_85 = lean_ctor_get(x_55, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_55);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_16);
if (x_180 == 0)
{
return x_16;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_16, 0);
x_182 = lean_ctor_get(x_16, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_16);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_14);
if (x_184 == 0)
{
return x_14;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_14, 0);
x_186 = lean_ctor_get(x_14, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_14);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_ctor_get(x_7, 0);
x_189 = lean_ctor_get(x_7, 2);
x_190 = lean_ctor_get(x_7, 3);
x_191 = lean_ctor_get(x_7, 4);
x_192 = lean_ctor_get(x_7, 5);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_7);
x_193 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_11);
lean_ctor_set(x_193, 2, x_189);
lean_ctor_set(x_193, 3, x_190);
lean_ctor_set(x_193, 4, x_191);
lean_ctor_set(x_193, 5, x_192);
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_194 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(x_2, x_5, x_6, x_193, x_8, x_9);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_196 = l_Lean_Meta_Match_isCurrVarInductive(x_2, x_5, x_6, x_193, x_8, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_244; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_244 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_2);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_2);
if (x_245 == 0)
{
uint8_t x_246; 
x_246 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_2);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_2);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_197);
x_248 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__1;
x_249 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_248, x_4, x_5, x_6, x_193, x_8, x_198);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_251 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(x_2, x_5, x_6, x_193, x_8, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_252, x_4, x_5, x_6, x_193, x_8, x_253);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_255 = lean_ctor_get(x_251, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_251, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_257 = x_251;
} else {
 lean_dec_ref(x_251);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
uint8_t x_259; 
x_259 = lean_unbox(x_197);
lean_dec(x_197);
if (x_259 == 0)
{
uint8_t x_260; 
x_260 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_2);
if (x_260 == 0)
{
lean_object* x_261; 
x_261 = lean_box(0);
x_199 = x_261;
goto block_243;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2;
x_263 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_262, x_4, x_5, x_6, x_193, x_8, x_198);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_265 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_2, x_5, x_6, x_193, x_8, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_266, x_4, x_5, x_6, x_193, x_8, x_267);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
}
else
{
uint8_t x_273; 
x_273 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_2);
if (x_273 == 0)
{
uint8_t x_274; 
x_274 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_2);
if (x_274 == 0)
{
lean_object* x_275; 
x_275 = lean_box(0);
x_199 = x_275;
goto block_243;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2;
x_277 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_276, x_4, x_5, x_6, x_193, x_8, x_198);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_279 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_2, x_5, x_6, x_193, x_8, x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_280, x_4, x_5, x_6, x_193, x_8, x_281);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_283 = lean_ctor_get(x_279, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_279, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_285 = x_279;
} else {
 lean_dec_ref(x_279);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
}
else
{
lean_object* x_287; 
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_287 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(x_2, x_5, x_6, x_193, x_8, x_198);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
x_291 = lean_array_get_size(x_288);
x_292 = lean_unsigned_to_nat(0u);
x_293 = lean_nat_dec_lt(x_292, x_291);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_294 = lean_box(0);
if (lean_is_scalar(x_290)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_290;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_289);
return x_295;
}
else
{
uint8_t x_296; 
x_296 = lean_nat_dec_le(x_291, x_291);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_297 = lean_box(0);
if (lean_is_scalar(x_290)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_290;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_289);
return x_298;
}
else
{
size_t x_299; size_t x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_290);
x_299 = 0;
x_300 = lean_usize_of_nat(x_291);
lean_dec(x_291);
x_301 = lean_box(0);
x_302 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_288, x_299, x_300, x_301, x_4, x_5, x_6, x_193, x_8, x_289);
lean_dec(x_288);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_303 = lean_ctor_get(x_287, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_287, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_305 = x_287;
} else {
 lean_dec_ref(x_287);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_197);
x_307 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__3;
x_308 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_307, x_4, x_5, x_6, x_193, x_8, x_198);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
x_310 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_2);
x_311 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_310, x_4, x_5, x_6, x_193, x_8, x_309);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_197);
x_312 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__4;
x_313 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_312, x_4, x_5, x_6, x_193, x_8, x_198);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_315 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(x_2, x_5, x_6, x_193, x_8, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_316, x_4, x_5, x_6, x_193, x_8, x_317);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_319 = lean_ctor_get(x_315, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_315, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_321 = x_315;
} else {
 lean_dec_ref(x_315);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
}
else
{
lean_object* x_323; 
lean_dec(x_197);
x_323 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(x_2, x_4, x_5, x_6, x_193, x_8, x_198);
return x_323;
}
block_243:
{
uint8_t x_200; 
lean_dec(x_199);
x_200 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_2);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_2);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(x_2, x_5, x_6, x_193, x_8, x_198);
return x_202;
}
else
{
lean_object* x_203; 
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_203 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(x_2, x_5, x_6, x_193, x_8, x_198);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = lean_array_get_size(x_204);
x_208 = lean_unsigned_to_nat(0u);
x_209 = lean_nat_dec_lt(x_208, x_207);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_210 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_206;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_205);
return x_211;
}
else
{
uint8_t x_212; 
x_212 = lean_nat_dec_le(x_207, x_207);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_213 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_206;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_205);
return x_214;
}
else
{
size_t x_215; size_t x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_206);
x_215 = 0;
x_216 = lean_usize_of_nat(x_207);
lean_dec(x_207);
x_217 = lean_box(0);
x_218 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_204, x_215, x_216, x_217, x_4, x_5, x_6, x_193, x_8, x_205);
lean_dec(x_204);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_219 = lean_ctor_get(x_203, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_203, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_221 = x_203;
} else {
 lean_dec_ref(x_203);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
else
{
lean_object* x_223; 
lean_inc(x_8);
lean_inc(x_193);
lean_inc(x_6);
lean_inc(x_5);
x_223 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(x_2, x_5, x_6, x_193, x_8, x_198);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = lean_array_get_size(x_224);
x_228 = lean_unsigned_to_nat(0u);
x_229 = lean_nat_dec_lt(x_228, x_227);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_227);
lean_dec(x_224);
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_230 = lean_box(0);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_225);
return x_231;
}
else
{
uint8_t x_232; 
x_232 = lean_nat_dec_le(x_227, x_227);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_227);
lean_dec(x_224);
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_233 = lean_box(0);
if (lean_is_scalar(x_226)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_226;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_225);
return x_234;
}
else
{
size_t x_235; size_t x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_226);
x_235 = 0;
x_236 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_237 = lean_box(0);
x_238 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_224, x_235, x_236, x_237, x_4, x_5, x_6, x_193, x_8, x_225);
lean_dec(x_224);
return x_238;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_239 = lean_ctor_get(x_223, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_223, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_241 = x_223;
} else {
 lean_dec_ref(x_223);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_324 = lean_ctor_get(x_196, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_196, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_326 = x_196;
} else {
 lean_dec_ref(x_196);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_193);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_328 = lean_ctor_get(x_194, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_194, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_330 = x_194;
} else {
 lean_dec_ref(x_194);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1(x_8, x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_14 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_level_eq(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dependent match elimination failed, universe level not found");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_levelZero;
x_9 = lean_level_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_List_redLength___rarg(x_1);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_12 = l_List_toArrayAux___rarg(x_1, x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(x_12, x_2, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__3;
x_16 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bootstrap");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("gen_matcher_code");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__2;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("disable code generation for auxiliary matcher function");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Data_Options___hyg_487____closed__3;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__1;
x_3 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__4;
x_3 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__6;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Lean_Meta_Match_generateMatcherCode(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__4;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_Match_generateMatcherCode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_generateMatcherCode(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Match_mkMatcher_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_Match_mkMatcher_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_map___at_Lean_Meta_Match_mkMatcher___spec__1(lean_object* x_1) {
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
x_8 = l_List_map___at_Lean_Meta_Match_mkMatcher___spec__1(x_5);
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
x_13 = l_List_map___at_Lean_Meta_Match_mkMatcher___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_5);
x_4 = x_9;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_List_map___at_Lean_Meta_Match_mkMatcher___spec__6(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Meta_Match_mkMatcher___spec__6(x_5);
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
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Meta_Match_mkMatcher___spec__6(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_HashSet_instInhabitedHashSet___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcher: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcher levels: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", uElim: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcher value: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ntype: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = 0;
x_19 = lean_box(0);
lean_inc(x_12);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_17, x_18, x_19, x_12, x_13, x_14, x_15, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_2);
x_23 = lean_array_to_list(lean_box(0), x_2);
lean_inc(x_23);
x_24 = l_List_map___at_Lean_Meta_Match_mkMatcher___spec__1(x_23);
x_25 = l_Lean_Expr_mvarId_x21(x_21);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_10);
lean_ctor_set(x_26, 3, x_24);
x_27 = lean_box(0);
x_28 = lean_st_ref_get(x_15, x_22);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__1;
x_31 = lean_st_mk_ref(x_30, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(x_26, x_32, x_12, x_13, x_14, x_15, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_15, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_32, x_37);
lean_dec(x_32);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_mkOptionalNode___closed__2;
x_42 = lean_array_push(x_41, x_3);
x_43 = l_Array_append___rarg(x_42, x_2);
lean_dec(x_2);
x_44 = lean_array_get_size(x_11);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = 0;
x_47 = x_11;
lean_inc(x_47);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(x_45, x_46, x_47);
x_49 = x_48;
x_50 = l_Array_append___rarg(x_43, x_49);
lean_dec(x_49);
lean_inc(x_12);
lean_inc(x_50);
x_51 = l_Lean_Meta_mkForallFVars(x_50, x_1, x_12, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_12);
x_54 = l_Lean_Meta_mkLambdaFVars(x_50, x_21, x_12, x_13, x_14, x_15, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_158; lean_object* x_159; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_172 = lean_st_ref_get(x_15, x_56);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 3);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_ctor_get_uint8(x_174, sizeof(void*)*1);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = 0;
x_158 = x_177;
x_159 = x_176;
goto block_171;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
lean_dec(x_172);
lean_inc(x_6);
x_179 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_6, x_12, x_13, x_14, x_15, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_158 = x_182;
x_159 = x_181;
goto block_171;
}
block_157:
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
x_59 = l_Lean_Meta_Match_generateMatcherCode(x_58);
lean_dec(x_58);
x_60 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_4);
x_61 = l_Lean_Meta_mkAuxDefinition(x_4, x_52, x_55, x_60, x_59, x_12, x_13, x_14, x_15, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_75; lean_object* x_76; lean_object* x_85; uint8_t x_126; lean_object* x_127; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_143 = lean_st_ref_get(x_15, x_63);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 3);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_ctor_get_uint8(x_145, sizeof(void*)*1);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_126 = x_60;
x_127 = x_147;
goto block_142;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
lean_inc(x_6);
x_149 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_6, x_12, x_13, x_14, x_15, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox(x_150);
lean_dec(x_150);
x_126 = x_152;
x_127 = x_151;
goto block_142;
}
block_74:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_List_lengthAux___rarg(x_5, x_66);
x_68 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
lean_inc(x_67);
x_69 = l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(x_68, x_39, x_67, x_67, x_27);
lean_dec(x_67);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
lean_dec(x_39);
x_71 = l_List_reverse___rarg(x_69);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_71);
if (lean_is_scalar(x_64)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_64;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
block_84:
{
if (x_75 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_65 = x_76;
goto block_74;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_62);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_62);
x_78 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__3;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_KernelException_toMessageData___closed__15;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_6, x_81, x_12, x_13, x_14, x_15, x_76);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_65 = x_83;
goto block_74;
}
}
block_125:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = l_Lean_Expr_getAppFn(x_62);
x_87 = l_Lean_Expr_constLevels_x21(x_86);
lean_dec(x_86);
x_88 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(x_87, x_7, x_12, x_13, x_14, x_15, x_85);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_91 = l_Lean_Meta_isLevelDefEq(x_7, x_8, x_12, x_13, x_14, x_15, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_Lean_Expr_getAppNumArgsAux(x_62, x_93);
x_95 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(x_45, x_46, x_47);
x_96 = x_95;
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_9);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_89);
lean_inc(x_4);
x_98 = l_Lean_Meta_Match_addMatcherInfo(x_4, x_97, x_12, x_13, x_14, x_15, x_92);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = 0;
x_101 = l_Lean_Meta_setInlineAttribute(x_4, x_100, x_12, x_13, x_14, x_15, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_st_ref_get(x_15, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 3);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_ctor_get_uint8(x_105, sizeof(void*)*1);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec(x_103);
x_75 = x_60;
x_76 = x_107;
goto block_84;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
lean_inc(x_6);
x_109 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_6, x_12, x_13, x_14, x_15, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_unbox(x_110);
lean_dec(x_110);
x_75 = x_112;
x_76 = x_111;
goto block_84;
}
}
else
{
uint8_t x_113; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_113 = !lean_is_exclusive(x_101);
if (x_113 == 0)
{
return x_101;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_101, 0);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_101);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_89);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_91);
if (x_117 == 0)
{
return x_91;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_91, 0);
x_119 = lean_ctor_get(x_91, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_91);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_88);
if (x_121 == 0)
{
return x_88;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_88, 0);
x_123 = lean_ctor_get(x_88, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_88);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
block_142:
{
if (x_126 == 0)
{
x_85 = x_127;
goto block_125;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_128 = l_Lean_Expr_getAppFn(x_62);
x_129 = l_Lean_Expr_constLevels_x21(x_128);
lean_dec(x_128);
x_130 = l_List_map___at_Lean_Meta_Match_mkMatcher___spec__6(x_129);
x_131 = l_Lean_MessageData_ofList(x_130);
lean_dec(x_130);
x_132 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__5;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__7;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_inc(x_7);
x_136 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_136, 0, x_7);
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_KernelException_toMessageData___closed__15;
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_inc(x_6);
x_140 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_6, x_139, x_12, x_13, x_14, x_15, x_127);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_85 = x_141;
goto block_125;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_153 = !lean_is_exclusive(x_61);
if (x_153 == 0)
{
return x_61;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_61, 0);
x_155 = lean_ctor_get(x_61, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_61);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
block_171:
{
if (x_158 == 0)
{
x_57 = x_159;
goto block_157;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_inc(x_55);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_55);
x_161 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__9;
x_162 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_Meta_Match_mkMatcher___lambda__1___closed__11;
x_164 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_52);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_52);
x_166 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_KernelException_toMessageData___closed__15;
x_168 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
lean_inc(x_6);
x_169 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_6, x_168, x_12, x_13, x_14, x_15, x_159);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_57 = x_170;
goto block_157;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_183 = !lean_is_exclusive(x_54);
if (x_183 == 0)
{
return x_54;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_54, 0);
x_185 = lean_ctor_get(x_54, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_54);
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
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_187 = !lean_is_exclusive(x_51);
if (x_187 == 0)
{
return x_51;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_51, 0);
x_189 = lean_ctor_get(x_51, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_51);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_34);
if (x_191 == 0)
{
return x_34;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_34, 0);
x_193 = lean_ctor_get(x_34, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_34);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("target: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motiveType: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_45; lean_object* x_46; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_st_ref_get(x_12, x_13);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 3);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get_uint8(x_58, sizeof(void*)*1);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = 0;
x_45 = x_61;
x_46 = x_60;
goto block_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_64 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_substCore___spec__14(x_63, x_9, x_10, x_11, x_12, x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_45 = x_67;
x_46 = x_66;
goto block_55;
}
block_44:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc(x_8);
x_15 = l_Lean_mkAppN(x_8, x_1);
x_32 = lean_st_ref_get(x_12, x_14);
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
x_16 = x_37;
x_17 = x_36;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_40 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_substCore___spec__14(x_39, x_9, x_10, x_11, x_12, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_16 = x_43;
x_17 = x_42;
goto block_31;
}
block_31:
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
lean_inc(x_3);
lean_inc(x_8);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__1___boxed), 16, 9);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_8);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_18);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_5);
lean_closure_set(x_19, 8, x_6);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(x_8, x_3, x_19, x_9, x_10, x_11, x_12, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_15);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = l_Lean_Meta_Match_mkMatcher___lambda__2___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_KernelException_toMessageData___closed__15;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_27 = l_Lean_addTrace___at_Lean_Meta_substCore___spec__13(x_26, x_25, x_9, x_10, x_11, x_12, x_17);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_3);
lean_inc(x_8);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__1___boxed), 16, 9);
lean_closure_set(x_29, 0, x_15);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_8);
lean_closure_set(x_29, 3, x_2);
lean_closure_set(x_29, 4, x_3);
lean_closure_set(x_29, 5, x_26);
lean_closure_set(x_29, 6, x_4);
lean_closure_set(x_29, 7, x_5);
lean_closure_set(x_29, 8, x_6);
x_30 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(x_8, x_3, x_29, x_9, x_10, x_11, x_12, x_28);
return x_30;
}
}
}
block_55:
{
if (x_45 == 0)
{
lean_dec(x_7);
x_14 = x_46;
goto block_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_7);
x_48 = l_Lean_Meta_Match_mkMatcher___lambda__2___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_KernelException_toMessageData___closed__15;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_53 = l_Lean_addTrace___at_Lean_Meta_substCore___spec__13(x_52, x_51, x_9, x_10, x_11, x_12, x_46);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_14 = x_54;
goto block_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_6);
x_12 = l_Lean_mkSort(x_6);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l_Lean_Meta_mkForallFVars(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__2), 13, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_6);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_14);
x_17 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
x_18 = 0;
x_19 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__7___rarg(x_17, x_18, x_14, x_16, x_7, x_8, x_9, x_10, x_15);
return x_19;
}
else
{
uint8_t x_20; 
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
}
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns(x_4, x_1, x_6, x_7, x_8, x_9, x_10);
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
x_13 = l_Lean_Meta_getLevel(x_5, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_levelZero;
x_17 = lean_level_eq(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_7, x_8, x_9, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_4, x_2, x_1, x_14, x_3, x_19, x_6, x_7, x_8, x_9, x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_4, x_2, x_1, x_14, x_3, x_16, x_6, x_7, x_8, x_9, x_15);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__4), 10, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Match_mkMatcher___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__2___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_5);
x_10 = l_Lean_Meta_mkLambdaFVars(x_3, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkLambdaFVars(x_2, x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
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
lean_dec(x_5);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1___boxed), 9, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
x_11 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__2___rarg(x_2, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected matcher application, insufficient number of parameters in alternative");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_2, x_9, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2(x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__3;
x_16 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_943____spec__1(x_15, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected type at MatcherApp.addArg");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = l_instInhabitedNat;
x_16 = lean_array_get(x_15, x_2, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_whnfD___at_Lean_Meta_getLevel___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 7)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_16);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3), 8, 1);
lean_closure_set(x_23, 0, x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2___rarg(x_20, x_22, x_23, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_expr_instantiate1(x_21, x_25);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_16, x_28);
lean_dec(x_16);
x_30 = lean_array_set(x_2, x_4, x_29);
x_31 = lean_array_fset(x_3, x_4, x_25);
x_32 = lean_nat_add(x_4, x_28);
lean_dec(x_4);
x_1 = x_27;
x_2 = x_30;
x_3 = x_31;
x_4 = x_32;
x_9 = x_26;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_dec(x_17);
x_39 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__3;
x_40 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1(x_39, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_MatcherApp_addArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_MatcherApp_addArg_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_MatcherApp_addArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Expr_isFVar(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_9);
x_14 = l_Lean_Expr_toHeadIndex(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_15);
x_17 = lean_st_ref_get(x_7, x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_st_mk_ref(x_19, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
x_23 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_14, x_16, x_11, x_15, x_21, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_16);
lean_dec(x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_7, x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_21, x_27);
lean_dec(x_21);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_21);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_box(0);
x_38 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_9);
x_39 = l_Lean_Expr_toHeadIndex(x_2);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_40);
x_42 = lean_st_ref_get(x_7, x_12);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_st_mk_ref(x_44, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_7);
x_48 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_39, x_41, x_11, x_40, x_46, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_41);
lean_dec(x_39);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_get(x_7, x_50);
lean_dec(x_7);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_get(x_46, x_52);
lean_dec(x_46);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_49);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_46);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = l_Lean_mkOptionalNode___closed__2;
x_63 = lean_array_push(x_62, x_2);
x_64 = lean_expr_abstract(x_11, x_63);
lean_dec(x_63);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_64);
return x_9;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_9, 0);
x_66 = lean_ctor_get(x_9, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_9);
x_67 = l_Lean_Expr_isFVar(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = l_Lean_Expr_toHeadIndex(x_2);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_69);
x_71 = lean_st_ref_get(x_7, x_66);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_st_mk_ref(x_73, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_7);
x_77 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_68, x_70, x_65, x_69, x_75, x_4, x_5, x_6, x_7, x_76);
lean_dec(x_70);
lean_dec(x_68);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_st_ref_get(x_7, x_79);
lean_dec(x_7);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_75, x_81);
lean_dec(x_75);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_75);
lean_dec(x_7);
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_88 = x_77;
} else {
 lean_dec_ref(x_77);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_box(0);
x_91 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_92 = l_Lean_Expr_toHeadIndex(x_2);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_93);
x_95 = lean_st_ref_get(x_7, x_66);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_st_mk_ref(x_97, x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_7);
x_101 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_92, x_94, x_65, x_93, x_99, x_4, x_5, x_6, x_7, x_100);
lean_dec(x_94);
lean_dec(x_92);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_st_ref_get(x_7, x_103);
lean_dec(x_7);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_get(x_99, x_105);
lean_dec(x_99);
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
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_99);
lean_dec(x_7);
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_112 = x_101;
} else {
 lean_dec_ref(x_101);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = l_Lean_mkOptionalNode___closed__2;
x_115 = lean_array_push(x_114, x_2);
x_116 = lean_expr_abstract(x_65, x_115);
lean_dec(x_115);
lean_dec(x_65);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_66);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_9);
if (x_118 == 0)
{
return x_9;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_9, 0);
x_120 = lean_ctor_get(x_9, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_9);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_array_get(x_14, x_2, x_13);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_array_get(x_14, x_16, x_13);
x_18 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_kabstract___at_Lean_Meta_MatcherApp_addArg___spec__1(x_4, x_17, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_expr_instantiate1(x_20, x_15);
lean_dec(x_15);
lean_dec(x_20);
x_3 = x_13;
x_4 = x_22;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_MatcherApp_addArg___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__4___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_inferType(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_2, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 7);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts(x_16, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_3);
x_29 = lean_ctor_get(x_2, 8);
lean_inc(x_29);
lean_dec(x_2);
x_30 = l_Array_append___rarg(x_28, x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_6);
lean_ctor_set(x_31, 4, x_7);
lean_ctor_set(x_31, 5, x_8);
lean_ctor_set(x_31, 6, x_24);
lean_ctor_set(x_31, 7, x_25);
lean_ctor_set(x_31, 8, x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
x_37 = l_Lean_mkOptionalNode___closed__2;
x_38 = lean_array_push(x_37, x_3);
x_39 = lean_ctor_get(x_2, 8);
lean_inc(x_39);
lean_dec(x_2);
x_40 = l_Array_append___rarg(x_38, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_6);
lean_ctor_set(x_41, 4, x_7);
lean_ctor_set(x_41, 5, x_8);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to add argument to matcher application, type error when constructing the new motive");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
x_12 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_inc(x_6);
x_16 = lean_array_to_list(lean_box(0), x_6);
lean_inc(x_15);
x_17 = l_Lean_mkConst(x_15, x_16);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
x_19 = l_Lean_mkAppN(x_17, x_18);
lean_inc(x_13);
x_20 = l_Lean_mkApp(x_19, x_13);
x_21 = l_Lean_mkAppN(x_20, x_4);
x_43 = lean_st_ref_get(x_10, x_14);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_22 = x_47;
goto block_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_524____closed__4;
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_substCore___spec__14(x_49, x_7, x_8, x_9, x_10, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_22 = x_53;
goto block_42;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
lean_inc(x_21);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_21);
x_56 = l_Lean_addTrace___at_Lean_Meta_substCore___spec__13(x_49, x_55, x_7, x_8, x_9, x_10, x_54);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_22 = x_57;
goto block_42;
}
}
block_42:
{
lean_object* x_23; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_23 = l_Lean_Meta_check(x_21, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_21);
x_25 = l_Lean_Meta_isTypeCorrect(x_21, x_7, x_8, x_9, x_10, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__3;
x_30 = l_Lean_throwError___at_Lean_Meta_MatcherApp_addArg___spec__3(x_29, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_MatcherApp_addArg___lambda__1(x_21, x_3, x_5, x_15, x_6, x_18, x_13, x_4, x_36, x_7, x_8, x_9, x_10, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_inferType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__2(x_2, x_3, x_15, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkArrow(x_17, x_4, x_6, x_7, x_8, x_9, x_18);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = l_Lean_Meta_MatcherApp_addArg___lambda__2(x_3, x_21, x_2, x_14, x_1, x_23, x_6, x_7, x_8, x_9, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_25);
x_28 = l_Lean_Meta_getLevel(x_25, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_array_set(x_31, x_27, x_29);
lean_dec(x_27);
x_33 = l_Lean_Meta_MatcherApp_addArg___lambda__2(x_3, x_25, x_2, x_14, x_1, x_32, x_6, x_7, x_8, x_9, x_30);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected matcher application, motive must be lambda expression with #");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_ctor_get(x_2, 5);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_nat_dec_eq(x_10, x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_19, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_MatcherApp_addArg___lambda__3(x_1, x_2, x_3, x_4, x_25, x_5, x_6, x_7, x_8, x_9);
return x_26;
}
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lambda__4), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__4___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_MatcherApp_addArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract___at_Lean_Meta_MatcherApp_addArg___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_MatcherApp_addArg___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_MatcherApp_addArg___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_MatcherApp_addArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_MatcherApp_addArg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_6139_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Util_Recognizers(lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
lean_object* initialize_Lean_Meta_Closure(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object*);
lean_object* initialize_Lean_Meta_GeneralizeTelescope(lean_object*);
lean_object* initialize_Lean_Meta_Match_Basic(lean_object*);
lean_object* initialize_Lean_Meta_Match_MVarRenaming(lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseValues(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Match_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_GeneralizeTelescope(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MVarRenaming(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseValues(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5);
l_Lean_Meta_Match_State_used___default___closed__1 = _init_l_Lean_Meta_Match_State_used___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_State_used___default___closed__1);
l_Lean_Meta_Match_State_used___default = _init_l_Lean_Meta_Match_State_used___default();
lean_mark_persistent(l_Lean_Meta_Match_State_used___default);
l_Lean_Meta_Match_State_counterExamples___default = _init_l_Lean_Meta_Match_State_counterExamples___default();
lean_mark_persistent(l_Lean_Meta_Match_State_counterExamples___default);
l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1 = _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1();
lean_mark_persistent(l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1);
l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2 = _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2();
lean_mark_persistent(l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2);
l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3 = _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3();
lean_mark_persistent(l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1);
l_Lean_Meta_Match_Unify_State_fvarSubst___default = _init_l_Lean_Meta_Match_Unify_State_fvarSubst___default();
lean_mark_persistent(l_Lean_Meta_Match_Unify_State_fvarSubst___default);
l_Lean_Meta_Match_Unify_assign___closed__1 = _init_l_Lean_Meta_Match_Unify_assign___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__1);
l_Lean_Meta_Match_Unify_assign___closed__2 = _init_l_Lean_Meta_Match_Unify_assign___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__2);
l_Lean_Meta_Match_Unify_assign___closed__3 = _init_l_Lean_Meta_Match_Unify_assign___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__3);
l_Lean_Meta_Match_Unify_assign___closed__4 = _init_l_Lean_Meta_Match_Unify_assign___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__4);
l_Lean_Meta_Match_Unify_assign___closed__5 = _init_l_Lean_Meta_Match_Unify_assign___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__5);
l_Lean_Meta_Match_Unify_assign___closed__6 = _init_l_Lean_Meta_Match_Unify_assign___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__6);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2___boxed__const__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2___boxed__const__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___closed__1);
l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__1 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__1);
l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2);
l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3);
l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4);
l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1);
l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2);
l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3);
l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4);
l_Lean_Meta_Match_processInaccessibleAsCtor___closed__5 = _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_processInaccessibleAsCtor___closed__5);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__1 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__1();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__1);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__2 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__2();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___boxed__const__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___boxed__const__1);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__4 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__4();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1);
l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1 = _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1();
lean_mark_persistent(l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1);
l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2 = _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2();
lean_mark_persistent(l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__3);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__3);
l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1 = _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1();
lean_mark_persistent(l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1);
l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2 = _init_l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2();
lean_mark_persistent(l_List_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___closed__1);
l_Lean_Meta_Match_isCurrVarInductive___closed__1 = _init_l_Lean_Meta_Match_isCurrVarInductive___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_isCurrVarInductive___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process___lambda__1___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__3);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__1 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__1();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__1);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__2 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__2();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__2);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__3 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__3();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__3);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__4 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__4();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__4);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__5 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__5();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__5);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__6 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__6();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159____closed__6);
res = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_5159_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__2);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__3 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__3);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__4 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__4);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__5 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__5);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__6 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__6);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__7 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__7);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__8 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__8);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__9 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__9);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__10 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__10);
l_Lean_Meta_Match_mkMatcher___lambda__1___closed__11 = _init_l_Lean_Meta_Match_mkMatcher___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__1___closed__11);
l_Lean_Meta_Match_mkMatcher___lambda__2___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__2___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__2___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__2___closed__2);
l_Lean_Meta_Match_mkMatcher___lambda__2___closed__3 = _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__2___closed__3);
l_Lean_Meta_Match_mkMatcher___lambda__2___closed__4 = _init_l_Lean_Meta_Match_mkMatcher___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__2___closed__4);
l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__3);
l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1);
l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2);
l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__3 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__3);
l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1);
l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_6139_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
