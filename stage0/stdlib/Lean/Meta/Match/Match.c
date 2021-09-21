// Lean compiler output
// Module: Lean.Meta.Match.Match
// Imports: Init Lean.Util.CollectLevelParams Lean.Util.Recognizers Lean.Compiler.ExternAttr Lean.Meta.Check Lean.Meta.Closure Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Contradiction Lean.Meta.GeneralizeTelescope Lean.Meta.Match.Basic Lean.Meta.Match.MVarRenaming Lean.Meta.Match.CaseValues
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
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__5;
lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__3;
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_List_get___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2;
uint8_t l_USize_decEq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___boxed(lean_object**);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__4;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_isAltVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed__const__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
lean_object* l_Lean_addTrace_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__1;
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5;
lean_object* l_Lean_Meta_dependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Unify_occurs(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__5;
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__6;
extern lean_object* l_Lean_Meta_Match_instInhabitedAlt;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3;
extern lean_object* l_instInhabitedNat;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__9___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___boxed(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2___boxed(lean_object**);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__3;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__13;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__8;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar___boxed(lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_matcherExt___closed__1;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4;
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1;
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop(lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_matcherExt___closed__2;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_State_fvarSubst___default;
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__9;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__4;
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__4;
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__6___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__7(lean_object*, lean_object*);
uint32_t l_UInt32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
size_t l_UInt64_toUSize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_9460_(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(uint8_t, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_mkHashSet___at_Lean_Meta_Match_State_used___default___spec__1(lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__2;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__7___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts(lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3(lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____lambda__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed(lean_object**);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__1;
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2;
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__9;
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__3;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4;
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4;
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Match_Unify_unify___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__2;
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_48____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(uint8_t, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_matcherExt;
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_State_counterExamples___default;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2;
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__9;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Unify_occurs___lambda__1(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed__const__1;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__8;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__3;
static lean_object* l_Lean_Meta_Match_Unify_unify___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(uint8_t, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3___boxed__const__1;
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__8;
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__8___closed__2;
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_List_elem___at_Lean_Occurrences_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___closed__1;
lean_object* l_Lean_mkSimpleThunkType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__1;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__8___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCurrVarInductive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_Match_instInhabitedPattern;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6;
lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_unify___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___boxed(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___boxed(lean_object**);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__8;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__3;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCurrVarInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___boxed(lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1;
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_assignGoalOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___boxed(lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__10;
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__6;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___boxed(lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1;
LEAN_EXPORT lean_object* l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__9;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__5;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(uint8_t, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1;
lean_object* l_Lean_Meta_Match_withGoalOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__17;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__11;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_unify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_expandIfVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_occurs___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Lean_Meta_Match_State_used___default___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_State_used___default;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_addInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_occurs___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__2;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1;
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__7;
LEAN_EXPORT lean_object* l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_bootstrap_genMatcherCode___closed__1;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___boxed(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableBool___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11;
static lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_bootstrap_genMatcherCode;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__6;
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(lean_object*, uint8_t, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_moveEntries___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2;
extern lean_object* l_Lean_Meta_Match_instInhabitedProblem;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__3;
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(uint8_t, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__5;
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2;
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_isAltVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_expandIfVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1;
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__7;
static lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__7;
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_9 = l_List_lengthTRAux___rarg(x_7, x_8);
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__2;
x_14 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = x_1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_apply_5(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkAppN(x_2, x_11);
x_14 = 0;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_3, x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1), 8, 3);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
x_21 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_9, x_20, x_4, x_5, x_6, x_7, x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__2;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
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
lean_dec(x_5);
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
lean_dec(x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_box(x_4);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed), 18, 12);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_21);
lean_closure_set(x_22, 4, x_5);
lean_closure_set(x_22, 5, x_6);
lean_closure_set(x_22, 6, x_7);
lean_closure_set(x_22, 7, x_8);
lean_closure_set(x_22, 8, x_9);
lean_closure_set(x_22, 9, x_10);
lean_closure_set(x_22, 10, x_11);
lean_closure_set(x_22, 11, x_12);
x_23 = 0;
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_13, x_23, x_14, x_22, x_16, x_17, x_18, x_19, x_20);
return x_24;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Match");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("debug");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("minor premise ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_71; lean_object* x_72; 
x_71 = lean_array_get_size(x_26);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_28);
lean_ctor_set(x_72, 1, x_71);
x_31 = x_72;
goto block_70;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = l_Lean_mkSimpleThunkType(x_28);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_31 = x_75;
goto block_70;
}
block_70:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_List_lengthTRAux___rarg(x_4, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_35, x_36);
x_38 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
x_39 = lean_name_append_index_after(x_38, x_37);
x_40 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8;
x_59 = lean_st_ref_get(x_9, x_29);
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
x_41 = x_64;
x_42 = x_63;
goto block_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_40, x_6, x_7, x_8, x_9, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_41 = x_69;
x_42 = x_68;
goto block_58;
}
block_58:
{
if (x_41 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(x_33, x_5, x_16, x_30, x_26, x_15, x_35, x_17, x_4, x_1, x_2, x_14, x_39, x_32, x_43, x_6, x_7, x_8, x_9, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_39);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_39);
x_46 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_32);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_32);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_40, x_53, x_6, x_7, x_8, x_9, x_42);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(x_33, x_5, x_16, x_30, x_26, x_15, x_35, x_17, x_4, x_1, x_2, x_14, x_39, x_32, x_55, x_6, x_7, x_8, x_9, x_56);
lean_dec(x_55);
return x_57;
}
}
}
}
else
{
uint8_t x_76; 
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
x_76 = !lean_is_exclusive(x_27);
if (x_76 == 0)
{
return x_27;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_27, 0);
x_78 = lean_ctor_get(x_27, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_27);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed(lean_object** _args) {
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
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_4);
lean_dec(x_4);
x_22 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(x_1, x_2, x_3, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_15);
return x_22;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(x_1, x_3, x_2, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_assignGoalOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Std_mkHashSet___at_Lean_Meta_Match_State_used___default___spec__1(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_isEmpty___rarg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 1;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_List_isEmpty___rarg(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; uint8_t x_7; 
x_6 = 1;
x_7 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(x_6, x_3);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = 1;
x_10 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(x_9, x_8);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 1;
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 1;
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
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
lean_dec(x_1);
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 0;
x_8 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Match.Match");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processSkipInaccessible");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(142u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = l_Lean_Meta_Match_instInhabitedAlt;
x_10 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4;
x_11 = lean_panic_fn(x_9, x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Meta_Match_instInhabitedAlt;
x_15 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4;
x_16 = lean_panic_fn(x_14, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_1 = x_13;
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_4, 4);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
lean_ctor_set(x_4, 4, x_24);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
lean_ctor_set(x_4, 4, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_2);
x_1 = x_20;
x_2 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_4, 2);
x_33 = lean_ctor_get(x_4, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_35 = x_5;
} else {
 lean_dec_ref(x_5);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_1 = x_20;
x_2 = x_37;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_5);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_5, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_5, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_Meta_Match_instInhabitedAlt;
x_44 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4;
x_45 = lean_panic_fn(x_43, x_44);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_45);
x_1 = x_42;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lean_Meta_Match_instInhabitedAlt;
x_49 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4;
x_50 = lean_panic_fn(x_48, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_2);
x_1 = x_47;
x_2 = x_51;
goto _start;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(138u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible(lean_object* x_1) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_7, x_10);
lean_ctor_set(x_1, 2, x_11);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_13, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_14);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceMsg");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_addTrace_addTraceOptions(x_11);
x_14 = lean_st_ref_take(x_7, x_12);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
x_23 = l_Lean_Name_append(x_1, x_22);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
x_30 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_9);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_21, x_33);
lean_ctor_set(x_16, 0, x_34);
x_35 = lean_st_ref_set(x_7, x_15, x_17);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
lean_dec(x_16);
x_44 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
x_45 = l_Lean_Name_append(x_1, x_44);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_47 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_13);
x_52 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_9);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Std_PersistentArray_push___rarg(x_43, x_55);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_42);
lean_ctor_set(x_15, 3, x_57);
x_58 = lean_st_ref_set(x_7, x_15, x_17);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
x_65 = lean_ctor_get(x_15, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_66 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_67 = lean_ctor_get(x_16, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_68 = x_16;
} else {
 lean_dec_ref(x_16);
 x_68 = lean_box(0);
}
x_69 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
x_70 = l_Lean_Name_append(x_1, x_69);
x_71 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_71, 0, x_1);
x_72 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_13);
x_77 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_9);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_9);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Std_PersistentArray_push___rarg(x_67, x_80);
if (lean_is_scalar(x_68)) {
 x_82 = lean_alloc_ctor(0, 1, 1);
} else {
 x_82 = x_68;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_66);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_63);
lean_ctor_set(x_83, 1, x_64);
lean_ctor_set(x_83, 2, x_65);
lean_ctor_set(x_83, 3, x_82);
x_84 = lean_st_ref_set(x_7, x_83, x_17);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = (size_t)x_9;
x_11 = lean_usize_modn(x_10, x_7);
lean_dec(x_7);
x_12 = lean_array_uget(x_2, x_11);
lean_ctor_set(x_3, 1, x_12);
x_13 = lean_array_uset(x_2, x_11, x_3);
x_2 = x_13;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_15);
x_18 = lean_apply_1(x_1, x_15);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = (size_t)x_19;
x_21 = lean_usize_modn(x_20, x_17);
lean_dec(x_17);
x_22 = lean_array_uget(x_2, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_uset(x_2, x_21, x_23);
x_2 = x_24;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__6___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = (size_t)x_7;
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 1, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_uint64_of_nat(x_13);
x_17 = (size_t)x_16;
x_18 = lean_usize_modn(x_17, x_15);
lean_dec(x_15);
x_19 = lean_array_uget(x_1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_uset(x_1, x_18, x_20);
x_1 = x_21;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSetImp_moveEntries___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__6___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashSetImp_moveEntries___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8(x_7, x_2, x_3);
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
x_13 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8(x_11, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_uint64_of_nat(x_2);
x_8 = (size_t)x_7;
x_9 = lean_usize_modn(x_8, x_6);
x_10 = lean_array_uget(x_5, x_9);
x_11 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_array_uset(x_5, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_6);
lean_dec(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_inc(x_2);
x_18 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8(x_10, x_2, x_2);
lean_dec(x_2);
x_19 = lean_array_uset(x_5, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_uint64_of_nat(x_2);
x_24 = (size_t)x_23;
x_25 = lean_usize_modn(x_24, x_22);
x_26 = lean_array_uget(x_21, x_25);
x_27 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_20, x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_array_uset(x_21, x_25, x_30);
x_32 = lean_nat_dec_le(x_29, x_22);
lean_dec(x_22);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(x_29, x_31);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_22);
lean_inc(x_2);
x_35 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8(x_26, x_2, x_2);
lean_dec(x_2);
x_36 = lean_array_uset(x_21, x_25, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc(x_8);
x_11 = l_Lean_Meta_admit(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_8, x_12);
lean_dec(x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_4, x_14);
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
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_16, 1, x_21);
x_22 = lean_st_ref_set(x_4, x_16, x_17);
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
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_17);
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
lean_dec(x_8);
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
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_unsigned_to_nat(16u);
x_3 = 0;
x_4 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing alternative");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l_Lean_Meta_contradictionCore(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_26 = lean_st_ref_get(x_6, x_14);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = 0;
x_16 = x_31;
x_17 = x_30;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unbox(x_34);
lean_dec(x_34);
x_16 = x_36;
x_17 = x_35;
goto block_25;
}
block_25:
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1(x_9, x_1, x_18, x_2, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__5;
x_21 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(x_15, x_20, x_2, x_3, x_4, x_5, x_6, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1(x_9, x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_2);
lean_dec(x_22);
lean_dec(x_1);
return x_24;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_11, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_11, 0, x_39);
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_dec(x_11);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
lean_dec(x_8);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
lean_inc(x_6);
x_49 = l_Lean_Meta_Match_assignGoalOf(x_1, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_get(x_6, x_50);
lean_dec(x_6);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_take(x_2, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_dec(x_47);
x_59 = l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(x_57, x_58);
lean_ctor_set(x_54, 0, x_59);
x_60 = lean_st_ref_set(x_2, x_54, x_55);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_54, 0);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_54);
x_69 = lean_ctor_get(x_47, 1);
lean_inc(x_69);
lean_dec(x_47);
x_70 = l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(x_67, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_72 = lean_st_ref_set(x_2, x_71, x_55);
lean_dec(x_2);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_49);
if (x_77 == 0)
{
return x_49;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_49, 0);
x_79 = lean_ctor_get(x_49, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_49);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; 
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
x_24 = lean_ctor_get(x_10, 4);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
x_13 = x_10;
x_14 = x_7;
goto block_23;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 5)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_10, 4);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
lean_ctor_set(x_24, 0, x_31);
lean_inc(x_1);
x_32 = l_Lean_Meta_Match_Alt_replaceFVarId(x_30, x_1, x_10);
x_13 = x_32;
x_14 = x_7;
goto block_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_10, 4, x_36);
lean_inc(x_1);
x_37 = l_Lean_Meta_Match_Alt_replaceFVarId(x_34, x_1, x_10);
x_13 = x_37;
x_14 = x_7;
goto block_23;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_10, 1);
x_40 = lean_ctor_get(x_10, 2);
x_41 = lean_ctor_get(x_10, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_10);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_43 = x_24;
} else {
 lean_dec_ref(x_24);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_40);
lean_ctor_set(x_47, 3, x_41);
lean_ctor_set(x_47, 4, x_46);
lean_inc(x_1);
x_48 = l_Lean_Meta_Match_Alt_replaceFVarId(x_44, x_1, x_47);
x_13 = x_48;
x_14 = x_7;
goto block_23;
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
x_13 = x_10;
x_14 = x_7;
goto block_23;
}
}
block_23:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_14);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_5);
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
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processAsPattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2;
x_3 = lean_unsigned_to_nat(160u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__3;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed), 10, 5);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_12);
lean_closure_set(x_16, 3, x_7);
lean_closure_set(x_16, 4, x_14);
x_17 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(199u);
x_4 = lean_unsigned_to_nat(40u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_29 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
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
x_74 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_5);
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
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(194u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___lambda__1), 10, 5);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_12);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_14);
x_18 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compile pattern matching, inductive type expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nhas type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_indentExpr(x_1);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_indentExpr(x_8);
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_2, x_3, x_1);
lean_dec(x_1);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_isAltVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_isAltVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_expandIfVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_expandIfVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Unify_occurs___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Unify_occurs(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_occurs___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_occurs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Match_Unify_occurs(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_addTrace_addTraceOptions(x_12);
x_15 = lean_st_ref_take(x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
x_24 = l_Lean_Name_append(x_1, x_23);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_26 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
x_31 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_10);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Std_PersistentArray_push___rarg(x_22, x_34);
lean_ctor_set(x_17, 0, x_35);
x_36 = lean_st_ref_set(x_8, x_16, x_18);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_43 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_dec(x_17);
x_45 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
x_46 = l_Lean_Name_append(x_1, x_45);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_14);
x_53 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_10);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Std_PersistentArray_push___rarg(x_44, x_56);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_43);
lean_ctor_set(x_16, 3, x_58);
x_59 = lean_st_ref_set(x_8, x_16, x_18);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_64 = lean_ctor_get(x_16, 0);
x_65 = lean_ctor_get(x_16, 1);
x_66 = lean_ctor_get(x_16, 2);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_16);
x_67 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_68 = lean_ctor_get(x_17, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_69 = x_17;
} else {
 lean_dec_ref(x_17);
 x_69 = lean_box(0);
}
x_70 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
x_71 = l_Lean_Name_append(x_1, x_70);
x_72 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_72, 0, x_1);
x_73 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_14);
x_78 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_10);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_10);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Std_PersistentArray_push___rarg(x_68, x_81);
if (lean_is_scalar(x_69)) {
 x_83 = lean_alloc_ctor(0, 1, 1);
} else {
 x_83 = x_69;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_67);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_64);
lean_ctor_set(x_84, 1, x_65);
lean_ctor_set(x_84, 2, x_66);
lean_ctor_set(x_84, 3, x_83);
x_85 = lean_st_ref_set(x_8, x_84, x_18);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_FVarSubst_insert(x_14, x_1, x_2);
x_17 = lean_st_ref_set(x_5, x_16, x_15);
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
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6;
x_2 = l_Lean_Meta_Match_Unify_assign___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Unify_assign___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assign failed variable is not local, ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Unify_assign___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Unify_assign___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assign occurs check failed, ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_assign___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Unify_assign___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Meta_Match_Unify_occurs(x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Match_Unify_isAltVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_36 = lean_st_ref_get(x_8, x_14);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = 0;
x_16 = x_41;
x_17 = x_40;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_16 = x_46;
x_17 = x_45;
goto block_35;
}
block_35:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Match_Unify_assign___closed__3;
if (x_16 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_8(x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = l_Lean_mkFVar(x_1);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Meta_Match_Unify_assign___closed__5;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_15, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_8(x_18, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_34;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_dec(x_11);
x_48 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_67 = lean_st_ref_get(x_8, x_47);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = 0;
x_49 = x_72;
x_50 = x_71;
goto block_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_unbox(x_75);
lean_dec(x_75);
x_49 = x_77;
x_50 = x_76;
goto block_66;
}
block_66:
{
if (x_49 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = l_Lean_Meta_Match_Unify_assign___lambda__2(x_1, x_2, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_inc(x_1);
x_53 = l_Lean_mkFVar(x_1);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_2);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_2);
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_62 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_48, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_Match_Unify_assign___lambda__2(x_1, x_2, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_63);
return x_65;
}
}
}
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_78 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_99 = lean_st_ref_get(x_8, x_9);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 3);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get_uint8(x_101, sizeof(void*)*1);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = 0;
x_79 = x_104;
x_80 = x_103;
goto block_98;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
x_106 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unbox(x_107);
lean_dec(x_107);
x_79 = x_109;
x_80 = x_108;
goto block_98;
}
block_98:
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Match_Unify_assign___closed__3;
if (x_79 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_apply_8(x_81, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_84 = l_Lean_mkFVar(x_1);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Lean_Meta_Match_Unify_assign___closed__9;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_89 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_2);
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_78, x_93, x_3, x_4, x_5, x_6, x_7, x_8, x_80);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_apply_8(x_81, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_96);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_Unify_assign___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Match_Unify_assign___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_unify___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_1);
x_15 = l_Lean_Meta_Match_Unify_expandIfVar(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_whnfD(x_16, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_2);
x_21 = l_Lean_Meta_Match_Unify_expandIfVar(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_whnfD(x_22, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_expr_eqv(x_1, x_19);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_Lean_Meta_Match_Unify_unify(x_19, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_expr_eqv(x_2, x_26);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_Meta_Match_Unify_unify(x_19, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_31;
}
else
{
lean_dec(x_26);
lean_dec(x_19);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_free_object(x_24);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Meta_Match_Unify_assign(x_32, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Meta_Match_Unify_assign(x_33, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_34, 0);
lean_dec(x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lean_Meta_Match_Unify_assign(x_47, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_48;
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_49; lean_object* x_50; 
lean_free_object(x_24);
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_Meta_Match_Unify_assign(x_49, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_50;
}
case 5:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_24);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_55 = l_Lean_Meta_Match_Unify_unify(x_51, x_53, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_55, 0);
lean_dec(x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_56);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = l_Lean_Meta_Match_Unify_unify(x_52, x_54, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_55);
if (x_64 == 0)
{
return x_55;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_55, 0);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_55);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
default: 
{
uint8_t x_68; lean_object* x_69; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = 0;
x_69 = lean_box(x_68);
lean_ctor_set(x_24, 0, x_69);
return x_24;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_70; lean_object* x_71; 
lean_free_object(x_24);
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
lean_dec(x_2);
x_71 = l_Lean_Meta_Match_Unify_assign(x_70, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = 0;
x_73 = lean_box(x_72);
lean_ctor_set(x_24, 0, x_73);
return x_24;
}
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
x_76 = lean_expr_eqv(x_1, x_19);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_2);
lean_dec(x_1);
x_77 = l_Lean_Meta_Match_Unify_unify(x_19, x_74, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
return x_77;
}
else
{
uint8_t x_78; 
x_78 = lean_expr_eqv(x_2, x_74);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_2);
lean_dec(x_1);
x_79 = l_Lean_Meta_Match_Unify_unify(x_19, x_74, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
return x_79;
}
else
{
lean_dec(x_74);
lean_dec(x_19);
switch (lean_obj_tag(x_1)) {
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_82 = l_Lean_Meta_Match_Unify_assign(x_80, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l_Lean_Meta_Match_Unify_assign(x_81, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_88 = x_82;
} else {
 lean_dec_ref(x_82);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_81);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_92 = x_82;
} else {
 lean_dec_ref(x_82);
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
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
lean_dec(x_1);
x_95 = l_Lean_Meta_Match_Unify_assign(x_94, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
return x_95;
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
lean_dec(x_2);
x_97 = l_Lean_Meta_Match_Unify_assign(x_96, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
return x_97;
}
case 5:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
lean_dec(x_1);
x_100 = lean_ctor_get(x_2, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_102 = l_Lean_Meta_Match_Unify_unify(x_98, x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_103);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_dec(x_102);
x_109 = l_Lean_Meta_Match_Unify_unify(x_99, x_101, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_112 = x_102;
} else {
 lean_dec_ref(x_102);
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
default: 
{
uint8_t x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = 0;
x_115 = lean_box(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_75);
return x_116;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
lean_dec(x_2);
x_118 = l_Lean_Meta_Match_Unify_assign(x_117, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
return x_118;
}
else
{
uint8_t x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_119 = 0;
x_120 = lean_box(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_75);
return x_121;
}
}
}
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_24);
if (x_122 == 0)
{
return x_24;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_24, 0);
x_124 = lean_ctor_get(x_24, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_24);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_9);
lean_dec(x_8);
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
else
{
uint8_t x_130; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_11);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_11, 0);
lean_dec(x_131);
x_132 = 1;
x_133 = lean_box(x_132);
lean_ctor_set(x_11, 0, x_133);
return x_11;
}
else
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_11, 1);
lean_inc(x_134);
lean_dec(x_11);
x_135 = 1;
x_136 = lean_box(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_11);
if (x_138 == 0)
{
return x_11;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_11, 0);
x_140 = lean_ctor_get(x_11, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_11);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_unify___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" =?= ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_Unify_unify___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_Unify_unify___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_unify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_10 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_28 = lean_st_ref_get(x_8, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = 0;
x_11 = x_33;
x_12 = x_32;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_11 = x_38;
x_12 = x_37;
goto block_27;
}
block_27:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Match_Unify_unify___lambda__1(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_1);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_Match_Unify_unify___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_2);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(x_10, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Match_Unify_unify___lambda__1(x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to unify ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("false");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
lean_inc(x_10);
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
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_19, x_25);
lean_dec(x_19);
x_27 = lean_unbox(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_58 = lean_st_ref_get(x_7, x_28);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = 0;
x_30 = x_63;
x_31 = x_62;
goto block_57;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_29, x_4, x_5, x_6, x_7, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_30 = x_68;
x_31 = x_67;
goto block_57;
}
block_57:
{
lean_object* x_32; 
x_32 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1;
if (x_30 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
lean_dec(x_10);
x_33 = lean_box(0);
x_34 = lean_apply_6(x_32, x_33, x_4, x_5, x_6, x_7, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_10);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Meta_Match_Unify_unify___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_unbox(x_22);
lean_dec(x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__6;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_29, x_44, x_4, x_5, x_6, x_7, x_31);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_6(x_32, x_46, x_4, x_5, x_6, x_7, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__9;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_29, x_52, x_4, x_5, x_6, x_7, x_31);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_apply_6(x_32, x_54, x_4, x_5, x_6, x_7, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_26);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_26, 0);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_26, 0, x_71);
return x_26;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_26, 0);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_26);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_12, 0);
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_9);
if (x_84 == 0)
{
return x_9;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_9, 0);
x_86 = lean_ctor_get(x_9, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_9);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_Pattern_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
x_10 = l_Lean_Meta_FVarSubst_get(x_1, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = 0;
x_13 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_11, x_12, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_14);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_16);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_18);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = l_Lean_Expr_fvarId_x21(x_20);
lean_dec(x_20);
x_23 = l_Lean_Meta_FVarSubst_get(x_1, x_22);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = 0;
x_26 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1(x_24, x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_23);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_3 = x_21;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_3 = x_21;
x_4 = x_31;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
x_3 = x_21;
x_4 = x_34;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_5);
x_12 = l_Lean_mkAppN(x_1, x_5);
lean_inc(x_3);
x_13 = l_Lean_Meta_Match_Alt_replaceFVarId(x_2, x_12, x_3);
x_14 = lean_array_get_size(x_5);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
lean_inc(x_5);
x_16 = x_5;
x_17 = lean_box_usize(x_15);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed__const__1;
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
x_26 = l_List_appendTR___rarg(x_24, x_25);
lean_inc(x_26);
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
x_41 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_38, x_40, x_39);
x_42 = lean_ctor_get(x_13, 4);
lean_inc(x_42);
x_43 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_38, x_42, x_39);
x_44 = lean_ctor_get(x_13, 2);
lean_inc(x_44);
lean_dec(x_13);
x_45 = l_Lean_Meta_FVarSubst_apply(x_38, x_44);
x_46 = lean_array_to_list(lean_box(0), x_5);
x_47 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_38, x_41, x_46, x_39);
lean_dec(x_38);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
lean_dec(x_3);
x_50 = l_List_appendTR___rarg(x_47, x_43);
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
x_55 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_52, x_54, x_53);
x_56 = lean_ctor_get(x_13, 4);
lean_inc(x_56);
x_57 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_52, x_56, x_53);
x_58 = lean_ctor_get(x_13, 2);
lean_inc(x_58);
lean_dec(x_13);
x_59 = l_Lean_Meta_FVarSubst_apply(x_52, x_58);
x_60 = lean_array_to_list(lean_box(0), x_5);
x_61 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_52, x_55, x_60, x_53);
lean_dec(x_52);
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
lean_dec(x_3);
x_64 = l_List_appendTR___rarg(x_61, x_57);
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
x_72 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_68, x_71, x_70);
x_73 = lean_ctor_get(x_13, 4);
lean_inc(x_73);
x_74 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_68, x_73, x_70);
x_75 = lean_ctor_get(x_13, 2);
lean_inc(x_75);
lean_dec(x_13);
x_76 = l_Lean_Meta_FVarSubst_apply(x_68, x_75);
x_77 = lean_array_to_list(lean_box(0), x_5);
x_78 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_68, x_72, x_77, x_70);
lean_dec(x_68);
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 1);
lean_inc(x_80);
lean_dec(x_3);
x_81 = l_List_appendTR___rarg(x_78, x_74);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_Meta_getLocalDecl(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_mkFVar(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_infer_type(x_13, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_whnfD(x_15, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_18);
x_20 = l_Lean_Meta_getInductiveUniverseAndParams(x_18, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_mkConst(x_2, x_23);
x_26 = l_Lean_mkAppN(x_25, x_24);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_26);
x_27 = lean_infer_type(x_26, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1), 11, 4);
lean_closure_set(x_30, 0, x_26);
lean_closure_set(x_30, 1, x_1);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_18);
x_31 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_28, x_30, x_4, x_5, x_6, x_7, x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
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
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__2), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_1);
x_11 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_10 = l_Lean_Meta_whnfD(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_16 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_15, x_2, x_3, x_4, x_5, x_13);
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
x_41 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_40, x_2, x_3, x_4, x_5, x_38);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_1);
lean_ctor_set(x_5, 3, x_10);
x_11 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_20 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
lean_ctor_set(x_21, 7, x_19);
x_22 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_2, x_3, x_4, x_21, x_6, x_7);
lean_dec(x_6);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_whnfD(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Expr_constructorApp_x3f(x_2, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = l_Lean_Meta_Match_Pattern_toMessageData(x_3);
x_21 = l_Lean_indentD(x_20);
x_22 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_4, x_25, x_10, x_11, x_12, x_13, x_18);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_name_eq(x_32, x_5);
lean_dec(x_5);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_34 = lean_box(0);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_29, 3);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_array_get_size(x_30);
x_37 = l_Array_extract___rarg(x_30, x_35, x_36);
x_38 = lean_array_to_list(lean_box(0), x_37);
x_39 = lean_box(0);
x_40 = l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_38, x_39);
x_41 = l_List_appendTR___rarg(x_40, x_6);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_7);
lean_ctor_set(x_42, 2, x_8);
lean_ctor_set(x_42, 3, x_9);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_19, 0, x_42);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
lean_dec(x_19);
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
x_48 = lean_name_eq(x_47, x_5);
lean_dec(x_5);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_49 = lean_box(0);
lean_ctor_set(x_15, 0, x_49);
return x_15;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_array_get_size(x_45);
x_52 = l_Array_extract___rarg(x_45, x_50, x_51);
x_53 = lean_array_to_list(lean_box(0), x_52);
x_54 = lean_box(0);
x_55 = l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_53, x_54);
x_56 = l_List_appendTR___rarg(x_55, x_6);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_7);
lean_ctor_set(x_57, 2, x_8);
lean_ctor_set(x_57, 3, x_9);
lean_ctor_set(x_57, 4, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_15, 0, x_58);
return x_15;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_15, 0);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_15);
x_61 = l_Lean_Expr_constructorApp_x3f(x_2, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = l_Lean_Meta_Match_Pattern_toMessageData(x_3);
x_63 = l_Lean_indentD(x_62);
x_64 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_4, x_67, x_10, x_11, x_12, x_13, x_60);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_70 = x_61;
} else {
 lean_dec_ref(x_61);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_name_eq(x_74, x_5);
lean_dec(x_5);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_60);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_71, 3);
lean_inc(x_78);
lean_dec(x_71);
x_79 = lean_array_get_size(x_72);
x_80 = l_Array_extract___rarg(x_72, x_78, x_79);
x_81 = lean_array_to_list(lean_box(0), x_80);
x_82 = lean_box(0);
x_83 = l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_81, x_82);
x_84 = l_List_appendTR___rarg(x_83, x_6);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_7);
lean_ctor_set(x_85, 2, x_8);
lean_ctor_set(x_85, 3, x_9);
lean_ctor_set(x_85, 4, x_84);
if (lean_is_scalar(x_70)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_70;
}
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_60);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
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
x_88 = !lean_is_exclusive(x_15);
if (x_88 == 0)
{
return x_15;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_15, 0);
x_90 = lean_ctor_get(x_15, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_15);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_9);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1), 14, 9);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_7);
lean_closure_set(x_16, 7, x_8);
lean_closure_set(x_16, 8, x_9);
x_17 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_9, x_16, x_11, x_12, x_13, x_14, x_15);
return x_17;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
x_3 = lean_unsigned_to_nat(340u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inaccessible in ctor step ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
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
x_25 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_40 = lean_st_ref_get(x_6, x_17);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = 0;
x_26 = x_45;
x_27 = x_44;
goto block_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_25, x_3, x_4, x_5, x_6, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox(x_48);
lean_dec(x_48);
x_26 = x_50;
x_27 = x_49;
goto block_39;
}
block_39:
{
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(x_23, x_24, x_15, x_18, x_2, x_22, x_19, x_20, x_21, x_28, x_3, x_4, x_5, x_6, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_23);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_23);
x_31 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_25, x_34, x_3, x_4, x_5, x_6, x_27);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(x_23, x_24, x_15, x_18, x_2, x_22, x_19, x_20, x_21, x_36, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_36);
return x_38;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_dec(x_8);
x_52 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_53 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2;
x_54 = lean_panic_fn(x_52, x_53);
x_55 = lean_apply_5(x_54, x_3, x_4, x_5, x_6, x_51);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 0;
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("the dependent pattern matcher can solve the following kinds of equations\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("- <var> = <term> and <term> = <var>\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("- <term> = <term> where the terms are definitionally equal\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__15;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" after processing");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample(x_1);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
if (x_10 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_2, 1, x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_Meta_Match_examplesToMessageData(x_27);
x_29 = l_Lean_indentD(x_28);
x_30 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_11);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_2, 1, x_43);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
lean_inc(x_1);
x_47 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample(x_1);
x_48 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
if (x_47 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_51 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_45);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_7);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_65 = lean_ctor_get(x_1, 3);
lean_inc(x_65);
lean_dec(x_1);
x_66 = l_Lean_Meta_Match_examplesToMessageData(x_65);
x_67 = l_Lean_indentD(x_66);
x_68 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_48);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_50);
lean_ctor_set(x_71, 1, x_70);
x_72 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_45);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_7);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_1);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_7);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_27 = x_11;
} else {
 lean_dec_ref(x_11);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_30; 
x_11 = l_Lean_Meta_saveState___rarg(x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Lean_Meta_Cases_cases(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = lean_apply_6(x_2, x_31, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_15 = x_34;
x_16 = x_35;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_14);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = l_List_isEmpty___rarg(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_14);
x_47 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg(x_1, x_43, x_6, x_7, x_8, x_9, x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_43);
lean_dec(x_1);
x_55 = lean_box(0);
x_15 = x_55;
x_16 = x_44;
goto block_29;
}
}
block_29:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_14);
x_17 = l_Lean_Meta_SavedState_restore(x_12, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; 
if (lean_is_scalar(x_14)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_14;
}
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
if (lean_is_scalar(x_14)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_14;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_box(1);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_19);
{
lean_object* _tmp_0 = x_17;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_1 = x_21;
x_2 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processConstructor");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__1;
x_3 = lean_unsigned_to_nat(408u);
x_4 = lean_unsigned_to_nat(48u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_22 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__2;
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
x_68 = l_List_appendTR___rarg(x_67, x_66);
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
x_76 = l_List_appendTR___rarg(x_75, x_74);
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
x_79 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_80 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__2;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_6);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_6;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_array_to_list(lean_box(0), x_21);
lean_inc(x_2);
lean_inc(x_23);
x_24 = l_List_appendTR___rarg(x_23, x_2);
x_25 = lean_box(0);
x_26 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(x_22, x_24, x_25);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(x_23, x_25);
lean_inc(x_27);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_ctor_get(x_1, 3);
lean_inc(x_30);
x_31 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(x_3, x_29, x_30, x_25);
lean_dec(x_29);
x_32 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(x_22, x_31, x_25);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_27, x_33, x_25);
x_35 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(x_22, x_34, x_25);
lean_dec(x_22);
x_36 = l_List_reverse___rarg(x_35);
lean_inc(x_20);
x_37 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___lambda__1), 11, 6);
lean_closure_set(x_37, 0, x_27);
lean_closure_set(x_37, 1, x_36);
lean_closure_set(x_37, 2, x_25);
lean_closure_set(x_37, 3, x_20);
lean_closure_set(x_37, 4, x_26);
lean_closure_set(x_37, 5, x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_20, x_37, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
x_42 = x_5 + x_41;
x_43 = x_39;
x_44 = lean_array_uset(x_17, x_5, x_43);
x_5 = x_42;
x_6 = x_44;
x_11 = x_40;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_List_isEmpty___rarg(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType), 6, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = l_Lean_Meta_Match_withGoalOf___rarg(x_3, x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
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
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__1;
x_3 = lean_unsigned_to_nat(361u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1;
x_13 = lean_panic_fn(x_11, x_12);
x_14 = lean_apply_5(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_19);
lean_inc(x_17);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___boxed), 9, 3);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_1);
x_22 = l_Lean_Expr_fvarId_x21(x_19);
lean_dec(x_19);
x_23 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_22);
lean_inc(x_16);
lean_inc(x_1);
x_24 = l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(x_1, x_21, x_16, x_22, x_23, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
lean_ctor_set(x_1, 1, x_20);
x_33 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_34 = lean_array_push(x_33, x_1);
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
lean_ctor_set(x_1, 1, x_20);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_37 = lean_array_push(x_36, x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_40 = x_24;
} else {
 lean_dec_ref(x_24);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_20);
lean_ctor_set(x_41, 2, x_17);
lean_ctor_set(x_41, 3, x_18);
x_42 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_43 = lean_array_push(x_42, x_41);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_40;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
lean_dec(x_25);
x_47 = lean_array_get_size(x_46);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = x_46;
x_50 = lean_box_usize(x_48);
x_51 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed__const__1;
x_52 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___boxed), 11, 6);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_20);
lean_closure_set(x_52, 2, x_22);
lean_closure_set(x_52, 3, x_50);
lean_closure_set(x_52, 4, x_51);
lean_closure_set(x_52, 5, x_49);
x_53 = x_52;
x_54 = lean_apply_5(x_53, x_3, x_4, x_5, x_6, x_45);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_24);
if (x_55 == 0)
{
return x_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_24, 0);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_24);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_18 = lean_st_ref_get(x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 0;
x_8 = x_23;
x_9 = x_22;
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_7, x_2, x_3, x_4, x_5, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
x_8 = x_28;
x_9 = x_27;
goto block_17;
}
block_17:
{
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2;
x_13 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_7, x_12, x_2, x_3, x_4, x_5, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(x_1, x_14, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processNonVariable");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(438u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compile pattern matching, unexpected pattern");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ndiscriminant");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_22 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2;
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
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
x_35 = lean_ctor_get(x_10, 2);
x_36 = lean_ctor_get(x_10, 3);
x_37 = lean_ctor_get(x_10, 4);
lean_dec(x_37);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_40 = l_Lean_Meta_isExprDefEq(x_1, x_39, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
lean_free_object(x_10);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_box(0);
x_13 = x_44;
x_14 = x_43;
goto block_19;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
lean_ctor_set(x_10, 4, x_38);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_10);
x_13 = x_46;
x_14 = x_45;
goto block_19;
}
}
else
{
uint8_t x_47; 
lean_dec(x_38);
lean_free_object(x_10);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
x_53 = lean_ctor_get(x_10, 2);
x_54 = lean_ctor_get(x_10, 3);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_dec(x_20);
x_56 = lean_ctor_get(x_31, 0);
lean_inc(x_56);
lean_dec(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_57 = l_Lean_Meta_isExprDefEq(x_1, x_56, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_box(0);
x_13 = x_61;
x_14 = x_60;
goto block_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_13 = x_64;
x_14 = x_62;
goto block_19;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
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
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_69 = l_Lean_Meta_Match_Pattern_toMessageData(x_31);
x_70 = l_Lean_indentD(x_69);
x_71 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_indentExpr(x_1);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_78, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
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
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(427u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compile pattern matching, inaccessible pattern or constructor expected");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_22 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1;
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
x_54 = l_List_appendTR___rarg(x_49, x_47);
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
x_67 = l_List_appendTR___rarg(x_62, x_60);
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
x_72 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_whnfD(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
x_18 = l_Lean_Expr_constructorApp_x3f(x_17, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_List_reverse___rarg(x_2);
x_20 = lean_box(0);
x_21 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(x_12, x_19, x_20, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_5);
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
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_12);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_List_reverse___rarg(x_2);
x_37 = lean_box(0);
lean_inc(x_34);
x_38 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2(x_34, x_36, x_37, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_34, 3);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_array_get_size(x_35);
x_43 = l_Array_extract___rarg(x_35, x_41, x_42);
x_44 = lean_array_to_list(lean_box(0), x_43);
x_45 = l_List_appendTR___rarg(x_44, x_4);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 3, x_5);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_ctor_get(x_34, 3);
lean_inc(x_49);
lean_dec(x_34);
x_50 = lean_array_get_size(x_35);
x_51 = l_Array_extract___rarg(x_35, x_49, x_50);
x_52 = lean_array_to_list(lean_box(0), x_51);
x_53 = l_List_appendTR___rarg(x_52, x_4);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
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
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_11, 0);
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(413u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1), 10, 5);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_12);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_14);
x_18 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Array_contains___at_Lean_Meta_CheckAssignment_checkFVar___spec__1(x_1, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
x_4 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; 
x_9 = l_List_reverse___rarg(x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_6, x_11);
lean_ctor_set(x_7, 1, x_8);
lean_ctor_set(x_7, 0, x_13);
{
lean_object* _tmp_4 = lean_box(0);
lean_object* _tmp_6 = x_12;
lean_object* _tmp_7 = x_7;
x_5 = _tmp_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_6, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_5 = lean_box(0);
x_7 = x_16;
x_8 = x_18;
goto _start;
}
}
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processValue");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
x_3 = lean_unsigned_to_nat(476u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = l_List_reverse___rarg(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 1);
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = l_Lean_Meta_Match_instInhabitedAlt;
x_17 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_18 = lean_panic_fn(x_16, x_17);
lean_ctor_set(x_8, 1, x_9);
lean_ctor_set(x_8, 0, x_18);
{
lean_object* _tmp_5 = lean_box(0);
lean_object* _tmp_7 = x_14;
lean_object* _tmp_8 = x_8;
x_6 = _tmp_5;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lean_Meta_Match_instInhabitedAlt;
x_22 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_23 = lean_panic_fn(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
x_6 = lean_box(0);
x_8 = x_20;
x_9 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 1:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_11, 4);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_12, 1);
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
lean_ctor_set(x_11, 4, x_31);
lean_inc(x_7);
x_34 = l_Lean_Meta_Match_Alt_replaceFVarId(x_33, x_7, x_11);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 0, x_34);
x_6 = lean_box(0);
x_8 = x_27;
x_9 = x_12;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
lean_ctor_set(x_11, 4, x_36);
lean_inc(x_7);
x_38 = l_Lean_Meta_Match_Alt_replaceFVarId(x_37, x_7, x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
x_6 = lean_box(0);
x_8 = x_27;
x_9 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
x_43 = lean_ctor_get(x_11, 2);
x_44 = lean_ctor_get(x_11, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_46 = x_12;
} else {
 lean_dec_ref(x_12);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_26, 0);
lean_inc(x_47);
lean_dec(x_26);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_44);
lean_ctor_set(x_48, 4, x_45);
lean_inc(x_7);
x_49 = l_Lean_Meta_Match_Alt_replaceFVarId(x_47, x_7, x_48);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_9);
x_6 = lean_box(0);
x_8 = x_27;
x_9 = x_50;
goto _start;
}
}
case 3:
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_26);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_11, 4);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_12, 1);
x_57 = lean_ctor_get(x_12, 0);
lean_dec(x_57);
lean_ctor_set(x_11, 4, x_56);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 0, x_11);
x_6 = lean_box(0);
x_8 = x_52;
x_9 = x_12;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
lean_dec(x_12);
lean_ctor_set(x_11, 4, x_59);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_9);
x_6 = lean_box(0);
x_8 = x_52;
x_9 = x_60;
goto _start;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_11, 0);
x_63 = lean_ctor_get(x_11, 1);
x_64 = lean_ctor_get(x_11, 2);
x_65 = lean_ctor_get(x_11, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_11);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_67 = x_12;
} else {
 lean_dec_ref(x_12);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set(x_68, 3, x_65);
lean_ctor_set(x_68, 4, x_66);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_9);
x_6 = lean_box(0);
x_8 = x_52;
x_9 = x_69;
goto _start;
}
}
default: 
{
uint8_t x_71; 
lean_dec(x_26);
lean_dec(x_11);
x_71 = !lean_is_exclusive(x_12);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_12, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_12, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
lean_dec(x_8);
x_75 = l_Lean_Meta_Match_instInhabitedAlt;
x_76 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_77 = lean_panic_fn(x_75, x_76);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 0, x_77);
x_6 = lean_box(0);
x_8 = x_74;
x_9 = x_12;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_12);
x_79 = lean_ctor_get(x_8, 1);
lean_inc(x_79);
lean_dec(x_8);
x_80 = l_Lean_Meta_Match_instInhabitedAlt;
x_81 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_82 = lean_panic_fn(x_80, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_9);
x_6 = lean_box(0);
x_8 = x_79;
x_9 = x_83;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_8, x_19);
lean_dec(x_8);
x_21 = lean_array_fget(x_7, x_9);
x_22 = lean_array_get_size(x_4);
x_23 = lean_nat_dec_lt(x_9, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
x_26 = lean_box(0);
x_27 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(x_24, x_26);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_inc(x_3);
lean_inc(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_25);
x_31 = lean_nat_add(x_9, x_19);
lean_dec(x_9);
x_32 = lean_array_push(x_11, x_30);
x_8 = x_20;
x_9 = x_31;
x_10 = lean_box(0);
x_11 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_array_fget(x_4, x_9);
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_21, 2);
lean_inc(x_36);
lean_inc(x_34);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
x_40 = lean_box(0);
x_41 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(x_5, x_37, x_39, x_40);
lean_dec(x_37);
x_42 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(x_36, x_41, x_40);
x_43 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(x_34, x_38, x_40);
x_44 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_1, x_6, x_9, x_21, lean_box(0), x_36, x_43, x_40);
x_45 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_4, x_6, x_9, x_21, lean_box(0), x_34, x_44, x_40);
lean_dec(x_21);
lean_inc(x_3);
x_46 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_36, x_3, x_40);
lean_dec(x_36);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_42);
x_48 = lean_nat_add(x_9, x_19);
lean_dec(x_9);
x_49 = lean_array_push(x_11, x_47);
x_8 = x_20;
x_9 = x_48;
x_10 = lean_box(0);
x_11 = x_49;
goto _start;
}
}
else
{
lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_16);
return x_51;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
x_3 = lean_unsigned_to_nat(455u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_3, x_4, x_5, x_6, x_7);
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
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_17);
x_19 = l_Lean_Meta_caseValues(x_16, x_17, x_15, x_18, x_3, x_4, x_5, x_6, x_7);
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
x_25 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(x_1, x_13, x_14, x_15, x_17, x_20, x_20, x_22, x_24, lean_box(0), x_23, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_18 = lean_st_ref_get(x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 0;
x_8 = x_23;
x_9 = x_22;
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_7, x_2, x_3, x_4, x_5, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
x_8 = x_28;
x_9 = x_27;
goto block_17;
}
block_17:
{
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2;
x_13 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_7, x_12, x_2, x_3, x_4, x_5, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(x_1, x_14, x_2, x_3, x_4, x_5, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_List_lengthTRAux___rarg(x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
x_4 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_fvarId_x21(x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_1, x_7);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_17 = lean_name_append_index_after(x_4, x_16);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___lambda__1), 12, 6);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_15);
x_19 = 0;
x_20 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_17, x_19, x_3, x_18, x_7, x_8, x_9, x_10, x_11);
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
x_22 = l_Lean_Meta_mkArrayLit(x_3, x_21, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_box(0);
x_30 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(x_21, x_29);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_25, 3);
x_35 = lean_ctor_get(x_25, 4);
x_36 = lean_ctor_get(x_25, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_25, 0);
lean_dec(x_37);
x_38 = l_List_appendTR___rarg(x_28, x_34);
x_39 = l_List_appendTR___rarg(x_30, x_35);
lean_ctor_set(x_25, 4, x_39);
lean_ctor_set(x_25, 3, x_38);
lean_ctor_set(x_25, 1, x_32);
lean_ctor_set(x_25, 0, x_31);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_25, 2);
x_41 = lean_ctor_get(x_25, 3);
x_42 = lean_ctor_get(x_25, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_25);
x_43 = l_List_appendTR___rarg(x_28, x_41);
x_44 = l_List_appendTR___rarg(x_30, x_42);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_32);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_26, 0, x_45);
return x_26;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_46 = lean_ctor_get(x_26, 0);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_26);
x_48 = lean_box(0);
x_49 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(x_21, x_48);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_ctor_get(x_25, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_25, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_25, 4);
lean_inc(x_54);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 x_55 = x_25;
} else {
 lean_dec_ref(x_25);
 x_55 = lean_box(0);
}
x_56 = l_List_appendTR___rarg(x_46, x_53);
x_57 = l_List_appendTR___rarg(x_49, x_54);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_56);
lean_ctor_set(x_58, 4, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_47);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_26);
if (x_60 == 0)
{
return x_26;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_26, 0);
x_62 = lean_ctor_get(x_26, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_22);
if (x_64 == 0)
{
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_getLocalDecl(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LocalDecl_userName(x_11);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(x_2, x_1, x_3, x_13, x_4, x_14, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1___boxed), 9, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
x_12 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_mkFVar(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_mkFVar(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_FVarSubst_apply(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_FVarSubst_apply(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_Meta_Match_Example_replaceFVarId(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Meta_Match_Example_applyFVarSubst(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_17 = l_List_lengthTRAux___rarg(x_15, x_16);
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
x_30 = l_List_lengthTRAux___rarg(x_28, x_29);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; 
x_9 = l_List_reverse___rarg(x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_6, x_11);
lean_ctor_set(x_7, 1, x_8);
lean_ctor_set(x_7, 0, x_13);
{
lean_object* _tmp_4 = lean_box(0);
lean_object* _tmp_6 = x_12;
lean_object* _tmp_7 = x_7;
x_5 = _tmp_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_6, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_5 = lean_box(0);
x_7 = x_16;
x_8 = x_18;
goto _start;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(533u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_36; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
x_36 = lean_ctor_get(x_18, 4);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_18);
x_37 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_38 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
x_39 = lean_panic_fn(x_37, x_38);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_40 = lean_apply_5(x_39, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_21 = x_41;
x_22 = x_42;
goto block_35;
}
else
{
uint8_t x_43; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
switch (lean_obj_tag(x_47)) {
case 1:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
x_51 = lean_ctor_get(x_18, 2);
x_52 = lean_ctor_get(x_18, 3);
x_53 = lean_ctor_get(x_18, 4);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_dec(x_36);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
lean_inc(x_2);
x_56 = l_Lean_Meta_FVarSubst_apply(x_9, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_57 = l_Lean_Meta_getArrayArgType(x_56, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_ctor_set(x_18, 4, x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
x_60 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(x_18, x_55, x_58, x_8, x_11, x_12, x_13, x_14, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_21 = x_61;
x_22 = x_62;
goto block_35;
}
else
{
uint8_t x_63; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_18);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_18, 0);
x_72 = lean_ctor_get(x_18, 1);
x_73 = lean_ctor_get(x_18, 2);
x_74 = lean_ctor_get(x_18, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_18);
x_75 = lean_ctor_get(x_36, 1);
lean_inc(x_75);
lean_dec(x_36);
x_76 = lean_ctor_get(x_47, 0);
lean_inc(x_76);
lean_dec(x_47);
lean_inc(x_2);
x_77 = l_Lean_Meta_FVarSubst_apply(x_9, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_78 = l_Lean_Meta_getArrayArgType(x_77, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_72);
lean_ctor_set(x_81, 2, x_73);
lean_ctor_set(x_81, 3, x_74);
lean_ctor_set(x_81, 4, x_75);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
x_82 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(x_81, x_76, x_79, x_8, x_11, x_12, x_13, x_14, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_21 = x_83;
x_22 = x_84;
goto block_35;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_87 = x_82;
} else {
 lean_dec_ref(x_82);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_89 = lean_ctor_get(x_78, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_91 = x_78;
} else {
 lean_dec_ref(x_78);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
case 4:
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_18);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_18, 4);
lean_dec(x_94);
x_95 = lean_ctor_get(x_36, 1);
lean_inc(x_95);
lean_dec(x_36);
x_96 = lean_ctor_get(x_47, 1);
lean_inc(x_96);
lean_dec(x_47);
x_97 = l_List_appendTR___rarg(x_96, x_95);
lean_ctor_set(x_18, 4, x_97);
x_21 = x_18;
x_22 = x_15;
goto block_35;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_18, 0);
x_99 = lean_ctor_get(x_18, 1);
x_100 = lean_ctor_get(x_18, 2);
x_101 = lean_ctor_get(x_18, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_18);
x_102 = lean_ctor_get(x_36, 1);
lean_inc(x_102);
lean_dec(x_36);
x_103 = lean_ctor_get(x_47, 1);
lean_inc(x_103);
lean_dec(x_47);
x_104 = l_List_appendTR___rarg(x_103, x_102);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_99);
lean_ctor_set(x_105, 2, x_100);
lean_ctor_set(x_105, 3, x_101);
lean_ctor_set(x_105, 4, x_104);
x_21 = x_105;
x_22 = x_15;
goto block_35;
}
}
default: 
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_47);
lean_dec(x_36);
lean_dec(x_18);
x_106 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_107 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
x_108 = lean_panic_fn(x_106, x_107);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_109 = lean_apply_5(x_108, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_21 = x_110;
x_22 = x_111;
goto block_35;
}
else
{
uint8_t x_112; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
block_35:
{
lean_object* x_23; 
x_23 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0), x_8, x_9, x_19, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_is_scalar(x_20)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_20;
}
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
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
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_20);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_8, x_19);
lean_dec(x_8);
x_21 = lean_array_fget(x_7, x_9);
x_22 = lean_array_get_size(x_4);
x_23 = lean_nat_dec_lt(x_9, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
x_26 = lean_box(0);
x_27 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(x_24, x_26);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_inc(x_3);
lean_inc(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_25);
x_31 = lean_nat_add(x_9, x_19);
lean_dec(x_9);
x_32 = lean_array_push(x_11, x_30);
x_8 = x_20;
x_9 = x_31;
x_10 = lean_box(0);
x_11 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = l_instInhabitedNat;
x_35 = lean_array_get(x_34, x_4, x_9);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 3);
lean_inc(x_38);
x_39 = lean_array_to_list(lean_box(0), x_37);
x_40 = lean_box(0);
lean_inc(x_39);
x_41 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(x_39, x_40);
lean_inc(x_3);
x_42 = l_List_appendTR___rarg(x_41, x_3);
x_43 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(x_38, x_42, x_40);
x_44 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__3(x_39, x_40);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
x_48 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(x_5, x_45, x_47, x_40);
lean_dec(x_45);
x_49 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(x_38, x_48, x_40);
x_50 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(x_35, x_46, x_40);
x_51 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(x_1, x_6, x_9, x_21, lean_box(0), x_38, x_50, x_40);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_2);
x_52 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(x_1, x_2, x_4, x_6, x_9, x_21, lean_box(0), x_35, x_38, x_51, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_38);
lean_dec(x_21);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_49);
x_56 = lean_nat_add(x_9, x_19);
lean_dec(x_9);
x_57 = lean_array_push(x_11, x_55);
x_8 = x_20;
x_9 = x_56;
x_10 = lean_box(0);
x_11 = x_57;
x_16 = x_54;
goto _start;
}
else
{
uint8_t x_59; 
lean_dec(x_49);
lean_dec(x_43);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_11);
lean_ctor_set(x_63, 1, x_16);
return x_63;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(509u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("x");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1;
x_11 = lean_panic_fn(x_9, x_10);
x_12 = lean_apply_5(x_11, x_3, x_4, x_5, x_6, x_7);
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
lean_inc(x_1);
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(x_1);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Lean_Expr_fvarId_x21(x_13);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3;
x_19 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_17);
x_20 = l_Lean_Meta_caseArraySizes(x_16, x_17, x_15, x_18, x_19, x_3, x_4, x_5, x_6, x_7);
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
x_26 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(x_1, x_13, x_14, x_15, x_17, x_21, x_21, x_23, x_25, lean_box(0), x_24, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("array literal step");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_18 = lean_st_ref_get(x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 0;
x_8 = x_23;
x_9 = x_22;
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_7, x_2, x_3, x_4, x_5, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
x_8 = x_28;
x_9 = x_27;
goto block_17;
}
block_17:
{
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1(x_1, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2;
x_13 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_7, x_12, x_2, x_3, x_4, x_5, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1(x_1, x_14, x_2, x_3, x_4, x_5, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__6;
x_3 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 3)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 9)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_4, 4);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = l_Lean_mkRawNatLit(x_29);
lean_ctor_set(x_13, 0, x_31);
lean_ctor_set(x_5, 1, x_30);
x_32 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4;
x_33 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_5);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_33);
lean_ctor_set(x_4, 4, x_1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_2);
x_1 = x_18;
x_2 = x_34;
goto _start;
}
else
{
lean_object* x_36; 
lean_dec(x_25);
lean_free_object(x_13);
x_36 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7;
lean_ctor_set(x_5, 0, x_36);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_18;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
lean_dec(x_16);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = l_Lean_mkRawNatLit(x_43);
lean_ctor_set(x_13, 0, x_45);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4;
x_48 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set(x_4, 4, x_1);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_2);
x_1 = x_18;
x_2 = x_49;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
lean_free_object(x_13);
x_51 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
lean_ctor_set(x_4, 4, x_52);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_18;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
x_56 = lean_ctor_get(x_4, 2);
x_57 = lean_ctor_get(x_4, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_4);
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_59 = x_5;
} else {
 lean_dec_ref(x_5);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_16, 0);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_60, x_63);
lean_dec(x_60);
x_65 = lean_box(0);
x_66 = l_Lean_mkRawNatLit(x_64);
lean_ctor_set(x_13, 0, x_66);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_13);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4;
x_69 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_69);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_56);
lean_ctor_set(x_70, 3, x_57);
lean_ctor_set(x_70, 4, x_1);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_2);
x_1 = x_18;
x_2 = x_71;
goto _start;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_60);
lean_free_object(x_13);
x_73 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7;
if (lean_is_scalar(x_59)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_59;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_58);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_54);
lean_ctor_set(x_75, 1, x_55);
lean_ctor_set(x_75, 2, x_56);
lean_ctor_set(x_75, 3, x_57);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_75);
{
lean_object* _tmp_0 = x_18;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
lean_dec(x_1);
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_4, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_82 = x_4;
} else {
 lean_dec_ref(x_4);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_5, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_84 = x_5;
} else {
 lean_dec_ref(x_5);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_16, 0);
lean_inc(x_85);
lean_dec(x_16);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_eq(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_85, x_88);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = l_Lean_mkRawNatLit(x_89);
lean_ctor_set(x_13, 0, x_91);
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_13);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4;
x_94 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_90);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_83);
if (lean_is_scalar(x_82)) {
 x_96 = lean_alloc_ctor(0, 5, 0);
} else {
 x_96 = x_82;
}
lean_ctor_set(x_96, 0, x_78);
lean_ctor_set(x_96, 1, x_79);
lean_ctor_set(x_96, 2, x_80);
lean_ctor_set(x_96, 3, x_81);
lean_ctor_set(x_96, 4, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_2);
x_1 = x_77;
x_2 = x_97;
goto _start;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_85);
lean_free_object(x_13);
x_99 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7;
if (lean_is_scalar(x_84)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_84;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_83);
if (lean_is_scalar(x_82)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_82;
}
lean_ctor_set(x_101, 0, x_78);
lean_ctor_set(x_101, 1, x_79);
lean_ctor_set(x_101, 2, x_80);
lean_ctor_set(x_101, 3, x_81);
lean_ctor_set(x_101, 4, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_2);
x_1 = x_77;
x_2 = x_102;
goto _start;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_16);
lean_free_object(x_13);
x_104 = !lean_is_exclusive(x_5);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_5, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_5, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_1, 1);
lean_inc(x_107);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_107;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_5);
x_109 = lean_ctor_get(x_1, 1);
lean_inc(x_109);
lean_dec(x_1);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_2);
x_1 = x_109;
x_2 = x_110;
goto _start;
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_13);
lean_dec(x_15);
x_112 = !lean_is_exclusive(x_5);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_5, 1);
lean_dec(x_113);
x_114 = lean_ctor_get(x_5, 0);
lean_dec(x_114);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_115;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_5);
x_117 = lean_ctor_get(x_1, 1);
lean_inc(x_117);
lean_dec(x_1);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_4);
lean_ctor_set(x_118, 1, x_2);
x_1 = x_117;
x_2 = x_118;
goto _start;
}
}
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_13, 0);
lean_inc(x_120);
lean_dec(x_13);
if (lean_obj_tag(x_120) == 9)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_122 = lean_ctor_get(x_1, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_123 = x_1;
} else {
 lean_dec_ref(x_1);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_4, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_4, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_4, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_4, 3);
lean_inc(x_127);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_128 = x_4;
} else {
 lean_dec_ref(x_4);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_5, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_130 = x_5;
} else {
 lean_dec_ref(x_5);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
lean_dec(x_121);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_nat_dec_eq(x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_sub(x_131, x_134);
lean_dec(x_131);
x_136 = lean_box(0);
x_137 = l_Lean_mkRawNatLit(x_135);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
x_140 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4;
x_141 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_136);
lean_ctor_set(x_141, 3, x_139);
if (lean_is_scalar(x_123)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_123;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_129);
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_124);
lean_ctor_set(x_143, 1, x_125);
lean_ctor_set(x_143, 2, x_126);
lean_ctor_set(x_143, 3, x_127);
lean_ctor_set(x_143, 4, x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_2);
x_1 = x_122;
x_2 = x_144;
goto _start;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
x_146 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7;
if (lean_is_scalar(x_130)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_130;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_129);
if (lean_is_scalar(x_128)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_128;
}
lean_ctor_set(x_148, 0, x_124);
lean_ctor_set(x_148, 1, x_125);
lean_ctor_set(x_148, 2, x_126);
lean_ctor_set(x_148, 3, x_127);
lean_ctor_set(x_148, 4, x_147);
if (lean_is_scalar(x_123)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_123;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_2);
x_1 = x_122;
x_2 = x_149;
goto _start;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_121);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_151 = x_5;
} else {
 lean_dec_ref(x_5);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_1, 1);
lean_inc(x_152);
lean_dec(x_1);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_4);
lean_ctor_set(x_153, 1, x_2);
x_1 = x_152;
x_2 = x_153;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_120);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_155 = x_5;
} else {
 lean_dec_ref(x_5);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_1, 1);
lean_inc(x_156);
lean_dec(x_1);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_4);
lean_ctor_set(x_157, 1, x_2);
x_1 = x_156;
x_2 = x_157;
goto _start;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_13);
x_159 = !lean_is_exclusive(x_5);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_5, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_5, 0);
lean_dec(x_161);
x_162 = lean_ctor_get(x_1, 1);
lean_inc(x_162);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_162;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_5);
x_164 = lean_ctor_get(x_1, 1);
lean_inc(x_164);
lean_dec(x_1);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_4);
lean_ctor_set(x_165, 1, x_2);
x_1 = x_164;
x_2 = x_165;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_box(0);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(x_3, x_4);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(x_8, x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
return x_12;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_20 = lean_st_ref_get(x_6, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = 0;
x_9 = x_25;
x_10 = x_24;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(x_8, x_2, x_3, x_4, x_5, x_6, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unbox(x_28);
lean_dec(x_28);
x_9 = x_30;
x_10 = x_29;
goto block_19;
}
block_19:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_stringToMessageData(x_1);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(x_8, x_17, x_2, x_3, x_4, x_5, x_6, x_10);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
lean_inc(x_1);
x_19 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_1, x_3, x_4, x_5, x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_Meta_Match_Problem_toMessageData(x_2, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_1, x_30, x_3, x_4, x_5, x_6, x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_Match_Problem_toMessageData(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_indentD(x_8);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCurrVarInductive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCurrVarInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Match_isCurrVarInductive___lambda__1), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_10);
x_18 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
x_12 = x_18;
x_13 = x_8;
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 2);
x_24 = lean_ctor_get(x_6, 3);
x_25 = lean_ctor_get(x_6, 4);
x_26 = lean_ctor_get(x_6, 5);
x_27 = lean_ctor_get(x_6, 6);
x_28 = lean_ctor_get(x_6, 7);
x_29 = l_Lean_replaceRef(x_20, x_24);
lean_dec(x_20);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_27);
lean_ctor_set(x_30, 7, x_28);
x_31 = 0;
lean_inc(x_7);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_31, x_19, x_4, x_5, x_30, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_35 = lean_infer_type(x_1, x_4, x_5, x_30, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_7);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_33);
x_38 = lean_infer_type(x_33, x_4, x_5, x_30, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_7);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_39);
lean_inc(x_36);
x_41 = l_Lean_Meta_isExprDefEq(x_36, x_39, x_4, x_5, x_30, x_7, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_11);
lean_dec(x_1);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_7);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_4);
x_45 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_39, x_36, x_4, x_5, x_30, x_7, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_indentExpr(x_33);
x_49 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__3;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
x_54 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_55, x_4, x_5, x_30, x_7, x_47);
lean_dec(x_7);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_61; lean_object* x_62; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_30);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_dec(x_41);
x_62 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
x_12 = x_62;
x_13 = x_61;
goto block_16;
}
}
else
{
uint8_t x_63; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_41);
if (x_63 == 0)
{
return x_41;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_38);
if (x_67 == 0)
{
return x_38;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_38, 0);
x_69 = lean_ctor_get(x_38, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_38);
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
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_35);
if (x_71 == 0)
{
return x_35;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_35, 0);
x_73 = lean_ctor_get(x_35, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_35);
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
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_32);
if (x_75 == 0)
{
return x_32;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_32, 0);
x_77 = lean_ctor_get(x_32, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_32);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
block_16:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_2 = x_11;
x_3 = x_14;
x_8 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1___boxed), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.List.moveToFront.loop");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1;
x_3 = lean_unsigned_to_nat(582u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(x_1, x_10, x_14);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_2, 1, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_free_object(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_3, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_3, x_26);
x_28 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(x_1, x_23, x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___closed__1;
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2(x_8, x_12);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_13, 1, x_1);
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
lean_ctor_set(x_1, 1, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_1);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_2, x_24);
x_26 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2(x_21, x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_instInhabitedPattern;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___closed__1;
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4(x_8, x_12);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_13, 1, x_1);
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
lean_ctor_set(x_1, 1, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_1);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_2, x_24);
x_26 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4(x_21, x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 4);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3(x_9, x_1);
lean_ctor_set(x_6, 4, x_10);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3(x_17, x_1);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_19);
{
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 4);
lean_inc(x_27);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 x_28 = x_21;
} else {
 lean_dec_ref(x_21);
 x_28 = lean_box(0);
}
x_29 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3(x_27, x_1);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 5, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
x_2 = x_22;
x_3 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = l_List_lengthTRAux___rarg(x_6, x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(x_6, x_2);
x_17 = lean_box(0);
x_18 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__5(x_2, x_7, x_17);
lean_ctor_set(x_1, 2, x_18);
lean_ctor_set(x_1, 1, x_16);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_19 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(x_6, x_2);
x_20 = lean_box(0);
x_21 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__5(x_2, x_7, x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_8);
return x_22;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__5(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.process.checkVarDeps");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1;
x_3 = lean_unsigned_to_nat(649u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2;
x_13 = lean_panic_fn(x_11, x_12);
x_14 = lean_apply_5(x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
x_19 = l_Lean_Expr_isFVar(x_15);
if (x_19 == 0)
{
x_1 = x_16;
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Expr_fvarId_x21(x_15);
lean_inc(x_3);
x_22 = l_Lean_Meta_dependsOn(x_3, x_21, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_1 = x_16;
x_2 = x_18;
x_8 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
lean_dec(x_28);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_8);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_List_lengthTRAux___rarg(x_8, x_9);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_14 = l_List_get___rarg(x_8, x_2, lean_box(0));
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_infer_type(x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps(x_8, x_2, x_16, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
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
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_2);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 == x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = x_2 + x_17;
x_2 = x_18;
x_4 = x_15;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nat value to constructor");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variable");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non variable");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("as-pattern");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_114; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_114 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_2);
if (x_114 == 0)
{
uint8_t x_115; 
lean_inc(x_2);
x_115 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_2);
if (x_115 == 0)
{
uint8_t x_116; 
lean_inc(x_2);
x_116 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_2);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_2);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_17);
x_118 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__3;
x_119 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_118, x_4, x_5, x_6, x_7, x_8, x_18);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_121 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(x_2, x_5, x_6, x_7, x_8, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_unsigned_to_nat(0u);
x_125 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_122, x_124, x_4, x_5, x_6, x_7, x_8, x_123);
return x_125;
}
else
{
uint8_t x_126; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_126 = !lean_is_exclusive(x_121);
if (x_126 == 0)
{
return x_121;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_121, 0);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_121);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
x_130 = lean_unbox(x_17);
lean_dec(x_17);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_box(0);
x_19 = x_131;
goto block_113;
}
else
{
uint8_t x_132; 
lean_inc(x_2);
x_132 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_2);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_box(0);
x_19 = x_133;
goto block_113;
}
else
{
lean_object* x_134; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_134 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(x_2, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_array_get_size(x_136);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_lt(x_139, x_138);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_141 = lean_box(0);
lean_ctor_set(x_134, 0, x_141);
return x_134;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_138, x_138);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_143 = lean_box(0);
lean_ctor_set(x_134, 0, x_143);
return x_134;
}
else
{
size_t x_144; size_t x_145; lean_object* x_146; lean_object* x_147; 
lean_free_object(x_134);
x_144 = 0;
x_145 = lean_usize_of_nat(x_138);
lean_dec(x_138);
x_146 = lean_box(0);
x_147 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_136, x_144, x_145, x_146, x_4, x_5, x_6, x_7, x_8, x_137);
lean_dec(x_136);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_134, 0);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_134);
x_150 = lean_array_get_size(x_148);
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_nat_dec_lt(x_151, x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
return x_154;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_150, x_150);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
return x_157;
}
else
{
size_t x_158; size_t x_159; lean_object* x_160; lean_object* x_161; 
x_158 = 0;
x_159 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_160 = lean_box(0);
x_161 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_148, x_158, x_159, x_160, x_4, x_5, x_6, x_7, x_8, x_149);
lean_dec(x_148);
return x_161;
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_162 = !lean_is_exclusive(x_134);
if (x_162 == 0)
{
return x_134;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_134, 0);
x_164 = lean_ctor_get(x_134, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_134);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_17);
x_166 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1;
x_167 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_166, x_4, x_5, x_6, x_7, x_8, x_18);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_2);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_169, x_170, x_4, x_5, x_6, x_7, x_8, x_168);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_17);
x_172 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__4;
x_173 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_172, x_4, x_5, x_6, x_7, x_8, x_18);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_175 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(x_2, x_5, x_6, x_7, x_8, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_176, x_178, x_4, x_5, x_6, x_7, x_8, x_177);
return x_179;
}
else
{
uint8_t x_180; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_180 = !lean_is_exclusive(x_175);
if (x_180 == 0)
{
return x_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_175, 0);
x_182 = lean_ctor_get(x_175, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_175);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
else
{
lean_object* x_184; 
lean_dec(x_17);
x_184 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(x_2, x_4, x_5, x_6, x_7, x_8, x_18);
return x_184;
}
block_113:
{
uint8_t x_20; 
lean_dec(x_19);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_2);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc(x_2);
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_2);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc(x_2);
x_22 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_2);
if (x_22 == 0)
{
uint8_t x_23; 
lean_inc(x_2);
x_23 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_2);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_24 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes(x_2, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(x_2, x_5, x_6, x_7, x_8, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1;
x_32 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_31, x_4, x_5, x_6, x_7, x_8, x_18);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_2);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_34, x_35, x_4, x_5, x_6, x_7, x_8, x_33);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(x_2, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_array_get_size(x_39);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = lean_box(0);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_41, x_41);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_box(0);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_37);
x_47 = 0;
x_48 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_49 = lean_box(0);
x_50 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_39, x_47, x_48, x_49, x_4, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_39);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_array_get_size(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_lt(x_54, x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_53, x_53);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
return x_60;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_63 = lean_box(0);
x_64 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_51, x_61, x_62, x_63, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_51);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
return x_37;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_37, 0);
x_67 = lean_ctor_get(x_37, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_37);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_69 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(x_2, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_array_get_size(x_71);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_lt(x_74, x_73);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = lean_box(0);
lean_ctor_set(x_69, 0, x_76);
return x_69;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_73, x_73);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_78 = lean_box(0);
lean_ctor_set(x_69, 0, x_78);
return x_69;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_69);
x_79 = 0;
x_80 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_81 = lean_box(0);
x_82 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_71, x_79, x_80, x_81, x_4, x_5, x_6, x_7, x_8, x_72);
lean_dec(x_71);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_69, 0);
x_84 = lean_ctor_get(x_69, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_69);
x_85 = lean_array_get_size(x_83);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_lt(x_86, x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
return x_89;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_85, x_85);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_95 = lean_box(0);
x_96 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_83, x_93, x_94, x_95, x_4, x_5, x_6, x_7, x_8, x_84);
lean_dec(x_83);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_69);
if (x_97 == 0)
{
return x_69;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_69, 0);
x_99 = lean_ctor_get(x_69, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_69);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__2;
x_102 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_101, x_4, x_5, x_6, x_7, x_8, x_18);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_104 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_2, x_5, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_105, x_107, x_4, x_5, x_6, x_7, x_8, x_106);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
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
uint8_t x_185; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_16);
if (x_185 == 0)
{
return x_16;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_16, 0);
x_187 = lean_ctor_get(x_16, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_16);
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
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_14);
if (x_189 == 0)
{
return x_14;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_14, 0);
x_191 = lean_ctor_get(x_14, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_14);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_193 = lean_ctor_get(x_7, 0);
x_194 = lean_ctor_get(x_7, 2);
x_195 = lean_ctor_get(x_7, 3);
x_196 = lean_ctor_get(x_7, 4);
x_197 = lean_ctor_get(x_7, 5);
x_198 = lean_ctor_get(x_7, 6);
x_199 = lean_ctor_get(x_7, 7);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_7);
x_200 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_200, 0, x_193);
lean_ctor_set(x_200, 1, x_11);
lean_ctor_set(x_200, 2, x_194);
lean_ctor_set(x_200, 3, x_195);
lean_ctor_set(x_200, 4, x_196);
lean_ctor_set(x_200, 5, x_197);
lean_ctor_set(x_200, 6, x_198);
lean_ctor_set(x_200, 7, x_199);
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_201 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(x_2, x_5, x_6, x_200, x_8, x_9);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_203 = l_Lean_Meta_Match_isCurrVarInductive(x_2, x_5, x_6, x_200, x_8, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_277; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_277 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_2);
if (x_277 == 0)
{
uint8_t x_278; 
lean_inc(x_2);
x_278 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_2);
if (x_278 == 0)
{
uint8_t x_279; 
lean_inc(x_2);
x_279 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_2);
if (x_279 == 0)
{
uint8_t x_280; 
x_280 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_2);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_204);
x_281 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__3;
x_282 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_281, x_4, x_5, x_6, x_200, x_8, x_205);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
x_284 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(x_2, x_5, x_6, x_200, x_8, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_unsigned_to_nat(0u);
x_288 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_285, x_287, x_4, x_5, x_6, x_200, x_8, x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_289 = lean_ctor_get(x_284, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_284, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_291 = x_284;
} else {
 lean_dec_ref(x_284);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
uint8_t x_293; 
x_293 = lean_unbox(x_204);
lean_dec(x_204);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_box(0);
x_206 = x_294;
goto block_276;
}
else
{
uint8_t x_295; 
lean_inc(x_2);
x_295 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_2);
if (x_295 == 0)
{
lean_object* x_296; 
x_296 = lean_box(0);
x_206 = x_296;
goto block_276;
}
else
{
lean_object* x_297; 
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
x_297 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(x_2, x_5, x_6, x_200, x_8, x_205);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_array_get_size(x_298);
x_302 = lean_unsigned_to_nat(0u);
x_303 = lean_nat_dec_lt(x_302, x_301);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_301);
lean_dec(x_298);
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_304 = lean_box(0);
if (lean_is_scalar(x_300)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_300;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_299);
return x_305;
}
else
{
uint8_t x_306; 
x_306 = lean_nat_dec_le(x_301, x_301);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_301);
lean_dec(x_298);
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_307 = lean_box(0);
if (lean_is_scalar(x_300)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_300;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_299);
return x_308;
}
else
{
size_t x_309; size_t x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_300);
x_309 = 0;
x_310 = lean_usize_of_nat(x_301);
lean_dec(x_301);
x_311 = lean_box(0);
x_312 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_298, x_309, x_310, x_311, x_4, x_5, x_6, x_200, x_8, x_299);
lean_dec(x_298);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_313 = lean_ctor_get(x_297, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_297, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_315 = x_297;
} else {
 lean_dec_ref(x_297);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_204);
x_317 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1;
x_318 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_317, x_4, x_5, x_6, x_200, x_8, x_205);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_2);
x_321 = lean_unsigned_to_nat(0u);
x_322 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_320, x_321, x_4, x_5, x_6, x_200, x_8, x_319);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_204);
x_323 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__4;
x_324 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_323, x_4, x_5, x_6, x_200, x_8, x_205);
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
lean_dec(x_324);
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
x_326 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(x_2, x_5, x_6, x_200, x_8, x_325);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_unsigned_to_nat(0u);
x_330 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_327, x_329, x_4, x_5, x_6, x_200, x_8, x_328);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_331 = lean_ctor_get(x_326, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_326, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_333 = x_326;
} else {
 lean_dec_ref(x_326);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
else
{
lean_object* x_335; 
lean_dec(x_204);
x_335 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(x_2, x_4, x_5, x_6, x_200, x_8, x_205);
return x_335;
}
block_276:
{
uint8_t x_207; 
lean_dec(x_206);
lean_inc(x_2);
x_207 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_2);
if (x_207 == 0)
{
uint8_t x_208; 
lean_inc(x_2);
x_208 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_2);
if (x_208 == 0)
{
uint8_t x_209; 
lean_inc(x_2);
x_209 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_2);
if (x_209 == 0)
{
uint8_t x_210; 
lean_inc(x_2);
x_210 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_2);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_211 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes(x_2, x_5, x_6, x_200, x_8, x_205);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(x_2, x_5, x_6, x_200, x_8, x_212);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_218 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1;
x_219 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_218, x_4, x_5, x_6, x_200, x_8, x_205);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_2);
x_222 = lean_unsigned_to_nat(0u);
x_223 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_221, x_222, x_4, x_5, x_6, x_200, x_8, x_220);
return x_223;
}
}
else
{
lean_object* x_224; 
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
x_224 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(x_2, x_5, x_6, x_200, x_8, x_205);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = lean_array_get_size(x_225);
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_nat_dec_lt(x_229, x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_231 = lean_box(0);
if (lean_is_scalar(x_227)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_227;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_226);
return x_232;
}
else
{
uint8_t x_233; 
x_233 = lean_nat_dec_le(x_228, x_228);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_234 = lean_box(0);
if (lean_is_scalar(x_227)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_227;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_226);
return x_235;
}
else
{
size_t x_236; size_t x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_227);
x_236 = 0;
x_237 = lean_usize_of_nat(x_228);
lean_dec(x_228);
x_238 = lean_box(0);
x_239 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_225, x_236, x_237, x_238, x_4, x_5, x_6, x_200, x_8, x_226);
lean_dec(x_225);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_240 = lean_ctor_get(x_224, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_224, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_242 = x_224;
} else {
 lean_dec_ref(x_224);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
}
else
{
lean_object* x_244; 
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
x_244 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(x_2, x_5, x_6, x_200, x_8, x_205);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = lean_array_get_size(x_245);
x_249 = lean_unsigned_to_nat(0u);
x_250 = lean_nat_dec_lt(x_249, x_248);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_248);
lean_dec(x_245);
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_251 = lean_box(0);
if (lean_is_scalar(x_247)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_247;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_246);
return x_252;
}
else
{
uint8_t x_253; 
x_253 = lean_nat_dec_le(x_248, x_248);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_248);
lean_dec(x_245);
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_254 = lean_box(0);
if (lean_is_scalar(x_247)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_247;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_246);
return x_255;
}
else
{
size_t x_256; size_t x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_247);
x_256 = 0;
x_257 = lean_usize_of_nat(x_248);
lean_dec(x_248);
x_258 = lean_box(0);
x_259 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_245, x_256, x_257, x_258, x_4, x_5, x_6, x_200, x_8, x_246);
lean_dec(x_245);
return x_259;
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_260 = lean_ctor_get(x_244, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_244, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_262 = x_244;
} else {
 lean_dec_ref(x_244);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__2;
x_265 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_264, x_4, x_5, x_6, x_200, x_8, x_205);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
lean_inc(x_8);
lean_inc(x_200);
lean_inc(x_6);
lean_inc(x_5);
x_267 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_2, x_5, x_6, x_200, x_8, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_unsigned_to_nat(0u);
x_271 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_268, x_270, x_4, x_5, x_6, x_200, x_8, x_269);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_272 = lean_ctor_get(x_267, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_267, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_274 = x_267;
} else {
 lean_dec_ref(x_267);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_336 = lean_ctor_get(x_203, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_203, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_338 = x_203;
} else {
 lean_dec_ref(x_203);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_200);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_340 = lean_ctor_get(x_201, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_201, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_342 = x_201;
} else {
 lean_dec_ref(x_201);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_341);
return x_343;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1(x_8, x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2;
x_14 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_set(x_8, x_1, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_10, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_set(x_6, x_2, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_19);
return x_20;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed with #");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", trying #");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_7, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess(x_19, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext___boxed), 7, 2);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_24);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_26 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_25, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_61 = lean_st_ref_get(x_7, x_32);
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
x_35 = x_66;
x_36 = x_65;
goto block_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(x_34, x_3, x_4, x_5, x_6, x_7, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_35 = x_71;
x_36 = x_70;
goto block_60;
}
block_60:
{
if (x_35 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___lambda__1(x_12, x_17, x_1, x_33, x_37, x_3, x_4, x_5, x_6, x_7, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = l_Nat_repr(x_2);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_33);
x_46 = l_Nat_repr(x_33);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Exception_toMessageData(x_21);
x_53 = l_Lean_indentD(x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
x_56 = l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(x_34, x_55, x_3, x_4, x_5, x_6, x_7, x_36);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___lambda__1(x_12, x_17, x_1, x_33, x_57, x_3, x_4, x_5, x_6, x_7, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_26);
if (x_72 == 0)
{
return x_26;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_26, 0);
x_74 = lean_ctor_get(x_26, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_26);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_2);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2;
x_16 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(x_15, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bootstrap");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("genMatcherCode");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__2;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("disable code generation for auxiliary matcher function");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__1;
x_3 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__4;
x_3 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__6;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_48____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Match_bootstrap_genMatcherCode___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____lambda__1(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
return x_2;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__2;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instHashableBool___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__4;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__8;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__9;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____lambda__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Match_matcherExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_matcherExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Match_matcherExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5;
x_3 = l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Environment");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.EnvExtensionInterfaceUnsafe.getState");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__2;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__3;
x_3 = lean_unsigned_to_nat(223u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__1;
x_8 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__4;
x_9 = lean_panic_fn(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_4, x_3);
x_11 = x_10;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_insert___rarg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_10);
lean_inc(x_1);
x_13 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_11, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_5);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1), 5, 4);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_4);
lean_closure_set(x_20, 3, x_5);
x_21 = l_Lean_Meta_Match_matcherExt;
x_22 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_21, x_19, x_20);
lean_ctor_set(x_16, 0, x_22);
x_23 = lean_st_ref_set(x_11, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_5);
x_25 = l_Lean_Meta_Match_addMatcherInfo(x_5, x_7, x_8, x_9, x_10, x_11, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_Meta_setInlineAttribute(x_5, x_27, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_28) == 0)
{
if (x_6 == 0)
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
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
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(x_1, x_8, x_9, x_10, x_11, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
x_43 = lean_ctor_get(x_16, 2);
x_44 = lean_ctor_get(x_16, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
lean_inc(x_5);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1), 5, 4);
lean_closure_set(x_45, 0, x_2);
lean_closure_set(x_45, 1, x_3);
lean_closure_set(x_45, 2, x_4);
lean_closure_set(x_45, 3, x_5);
x_46 = l_Lean_Meta_Match_matcherExt;
x_47 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_46, x_41, x_45);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_44);
x_49 = lean_st_ref_set(x_11, x_48, x_17);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_5);
x_51 = l_Lean_Meta_Match_addMatcherInfo(x_5, x_7, x_8, x_9, x_10, x_11, x_50);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_54 = l_Lean_Meta_setInlineAttribute(x_5, x_53, x_8, x_9, x_10, x_11, x_52);
if (lean_obj_tag(x_54) == 0)
{
if (x_6 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
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
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(x_1, x_8, x_9, x_10, x_11, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_63 = x_54;
} else {
 lean_dec_ref(x_54);
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
}
else
{
uint8_t x_65; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
return x_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_ctor_get(x_13, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_13);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_box(x_6);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___boxed), 12, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_14);
x_16 = lean_ctor_get(x_7, 3);
lean_inc(x_16);
x_17 = lean_array_to_list(lean_box(0), x_16);
x_18 = l_Lean_mkConst(x_5, x_17);
x_19 = lean_ctor_get(x_7, 4);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lean_mkAppN(x_18, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = l_Lean_Meta_Match_bootstrap_genMatcherCode;
x_13 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_11, x_12);
lean_dec(x_11);
x_14 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_Closure_mkValueTypeClosure(x_1, x_2, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_9, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Match_matcherExt;
x_24 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(x_23, x_22);
x_25 = lean_ctor_get(x_16, 2);
lean_inc(x_25);
x_26 = lean_box(x_13);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3;
x_29 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5;
lean_inc(x_27);
x_30 = l_Std_PersistentHashMap_find_x3f___rarg(x_28, x_29, x_24, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint32_t x_37; uint32_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
lean_free_object(x_18);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_array_to_list(lean_box(0), x_31);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_33);
lean_inc(x_3);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_25);
lean_inc(x_22);
x_35 = l_Lean_getMaxHeight(x_22, x_25);
x_36 = lean_unbox_uint32(x_35);
lean_dec(x_35);
x_37 = 1;
x_38 = x_36 + x_37;
x_39 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_39, 0, x_38);
lean_inc(x_33);
lean_inc(x_22);
x_40 = l_Lean_Environment_hasUnsafe(x_22, x_33);
if (x_40 == 0)
{
uint8_t x_76; 
lean_inc(x_25);
x_76 = l_Lean_Environment_hasUnsafe(x_22, x_25);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 1;
x_41 = x_77;
goto block_75;
}
else
{
uint8_t x_78; 
x_78 = 0;
x_41 = x_78;
goto block_75;
}
}
else
{
uint8_t x_79; 
lean_dec(x_22);
x_79 = 0;
x_41 = x_79;
goto block_75;
}
block_75:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_inc(x_25);
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_65 = lean_st_ref_get(x_9, x_21);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_44 = x_14;
x_45 = x_69;
goto block_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
lean_inc(x_4);
x_71 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_4, x_6, x_7, x_8, x_9, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_72);
lean_dec(x_72);
x_44 = x_74;
x_45 = x_73;
goto block_64;
}
block_64:
{
if (x_44 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
lean_dec(x_25);
lean_dec(x_4);
x_46 = lean_box(0);
x_47 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_43, x_28, x_29, x_27, x_3, x_13, x_16, x_46, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_inc(x_3);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_3);
x_49 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_33);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_25);
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
x_60 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_4, x_59, x_6, x_7, x_8, x_9, x_45);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_43, x_28, x_29, x_27, x_3, x_13, x_16, x_61, x_6, x_7, x_8, x_9, x_62);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_61);
return x_63;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_ctor_get(x_30, 0);
lean_inc(x_80);
lean_dec(x_30);
x_81 = lean_ctor_get(x_16, 3);
lean_inc(x_81);
x_82 = lean_array_to_list(lean_box(0), x_81);
x_83 = l_Lean_mkConst(x_80, x_82);
x_84 = lean_ctor_get(x_16, 4);
lean_inc(x_84);
lean_dec(x_16);
x_85 = l_Lean_mkAppN(x_83, x_84);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_18, 0, x_87);
return x_18;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_18, 0);
x_89 = lean_ctor_get(x_18, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_18);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Meta_Match_matcherExt;
x_92 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(x_91, x_90);
x_93 = lean_ctor_get(x_16, 2);
lean_inc(x_93);
x_94 = lean_box(x_13);
lean_inc(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3;
x_97 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5;
lean_inc(x_95);
x_98 = l_Std_PersistentHashMap_find_x3f___rarg(x_96, x_97, x_92, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint32_t x_104; uint32_t x_105; uint32_t x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; 
x_99 = lean_ctor_get(x_16, 0);
lean_inc(x_99);
x_100 = lean_array_to_list(lean_box(0), x_99);
x_101 = lean_ctor_get(x_16, 1);
lean_inc(x_101);
lean_inc(x_101);
lean_inc(x_3);
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_3);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_101);
lean_inc(x_93);
lean_inc(x_90);
x_103 = l_Lean_getMaxHeight(x_90, x_93);
x_104 = lean_unbox_uint32(x_103);
lean_dec(x_103);
x_105 = 1;
x_106 = x_104 + x_105;
x_107 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_107, 0, x_106);
lean_inc(x_101);
lean_inc(x_90);
x_108 = l_Lean_Environment_hasUnsafe(x_90, x_101);
if (x_108 == 0)
{
uint8_t x_144; 
lean_inc(x_93);
x_144 = l_Lean_Environment_hasUnsafe(x_90, x_93);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = 1;
x_109 = x_145;
goto block_143;
}
else
{
uint8_t x_146; 
x_146 = 0;
x_109 = x_146;
goto block_143;
}
}
else
{
uint8_t x_147; 
lean_dec(x_90);
x_147 = 0;
x_109 = x_147;
goto block_143;
}
block_143:
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_inc(x_93);
x_110 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_110, 0, x_102);
lean_ctor_set(x_110, 1, x_93);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_133 = lean_st_ref_get(x_9, x_89);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 3);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_ctor_get_uint8(x_135, sizeof(void*)*1);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
x_112 = x_14;
x_113 = x_137;
goto block_132;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_dec(x_133);
lean_inc(x_4);
x_139 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_4, x_6, x_7, x_8, x_9, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_unbox(x_140);
lean_dec(x_140);
x_112 = x_142;
x_113 = x_141;
goto block_132;
}
block_132:
{
if (x_112 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_101);
lean_dec(x_93);
lean_dec(x_4);
x_114 = lean_box(0);
x_115 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_111, x_96, x_97, x_95, x_3, x_13, x_16, x_114, x_6, x_7, x_8, x_9, x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_3);
x_116 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_116, 0, x_3);
x_117 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_121, 0, x_101);
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_125, 0, x_93);
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_117);
x_128 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_4, x_127, x_6, x_7, x_8, x_9, x_113);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_111, x_96, x_97, x_95, x_3, x_13, x_16, x_129, x_6, x_7, x_8, x_9, x_130);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_129);
return x_131;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_98, 0);
lean_inc(x_148);
lean_dec(x_98);
x_149 = lean_ctor_get(x_16, 3);
lean_inc(x_149);
x_150 = lean_array_to_list(lean_box(0), x_149);
x_151 = l_Lean_mkConst(x_148, x_150);
x_152 = lean_ctor_get(x_16, 4);
lean_inc(x_152);
lean_dec(x_16);
x_153 = l_Lean_mkAppN(x_151, x_152);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_89);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_15);
if (x_157 == 0)
{
return x_15;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_15, 0);
x_159 = lean_ctor_get(x_15, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_15);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__4;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_9 = l_Lean_Meta_Match_mkMatcherAuxDefinition___closed__1;
x_31 = lean_st_ref_get(x_7, x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_10 = x_36;
x_11 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_9, x_4, x_5, x_6, x_7, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_10 = x_41;
x_11 = x_40;
goto block_30;
}
block_30:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4(x_2, x_3, x_1, x_9, x_12, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_1);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_3);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
x_26 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_9, x_25, x_4, x_5, x_6, x_7, x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4(x_2, x_3, x_1, x_9, x_27, x_4, x_5, x_6, x_7, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_fvarId_x21(x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_List_lengthTRAux___rarg(x_1, x_13);
lean_inc(x_14);
x_15 = l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(x_2, x_3, x_14, x_14, x_4);
lean_dec(x_14);
x_16 = lean_ctor_get(x_3, 1);
x_17 = l_List_reverse___rarg(x_15);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcher: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__2___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Expr_getAppFn(x_1);
x_21 = l_Lean_Expr_constLevels_x21(x_20);
lean_dec(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_22 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(x_21, x_2, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_25 = l_Lean_Meta_isLevelDefEq(x_2, x_3, x_15, x_16, x_17, x_18, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_18, x_26);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_54; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
x_54 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3;
x_28 = x_54;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_9, 0);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Lean_Expr_getAppNumArgsAux(x_1, x_56);
x_58 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(x_10, x_11, x_12);
x_59 = x_58;
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_13);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_23);
x_61 = lean_apply_1(x_55, x_60);
x_28 = x_61;
goto block_53;
}
block_53:
{
uint8_t x_29; lean_object* x_30; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_27, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_dec(x_27);
x_47 = 0;
x_29 = x_47;
x_30 = x_46;
goto block_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_dec(x_27);
lean_inc(x_8);
x_49 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_8, x_15, x_16, x_17, x_18, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_29 = x_52;
x_30 = x_51;
goto block_42;
}
block_42:
{
if (x_29 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_Match_mkMatcher___lambda__1(x_4, x_5, x_6, x_7, x_1, x_28, x_31, x_15, x_16, x_17, x_18, x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_1);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_8, x_37, x_15, x_16, x_17, x_18, x_30);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Match_mkMatcher___lambda__1(x_4, x_5, x_6, x_7, x_1, x_28, x_39, x_15, x_16, x_17, x_18, x_40);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_41;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_25);
if (x_62 == 0)
{
return x_25;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_25, 0);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_25);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_22);
if (x_66 == 0)
{
return x_22;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_22, 0);
x_68 = lean_ctor_get(x_22, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_22);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcher levels: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", uElim: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_dec(x_15);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_Meta_Match_mkMatcherAuxDefinition(x_1, x_2, x_3, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_47 = lean_st_ref_get(x_19, x_23);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 3);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*1);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = 0;
x_26 = x_52;
x_27 = x_51;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
lean_inc(x_10);
x_54 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_10, x_16, x_17, x_18, x_19, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unbox(x_55);
lean_dec(x_55);
x_26 = x_57;
x_27 = x_56;
goto block_46;
}
block_46:
{
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25, x_11, x_12, x_13, x_14, x_28, x_16, x_17, x_18, x_19, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = l_Lean_Expr_getAppFn(x_24);
x_31 = l_Lean_Expr_constLevels_x21(x_30);
lean_dec(x_30);
lean_inc(x_9);
x_32 = l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__6(x_31, x_9);
x_33 = l_Lean_MessageData_ofList(x_32);
lean_dec(x_32);
x_34 = l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_4);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_4);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_10);
x_42 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_10, x_41, x_16, x_17, x_18, x_19, x_27);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25, x_11, x_12, x_13, x_14, x_43, x_16, x_17, x_18, x_19, x_44);
lean_dec(x_43);
return x_45;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_21);
if (x_58 == 0)
{
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_21, 0);
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_21);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcher value: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ntype: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_24 = lean_box(0);
lean_inc(x_23);
x_25 = l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__1(x_23, x_24);
x_26 = l_Lean_Expr_mvarId_x21(x_21);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_10);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_st_ref_get(x_15, x_22);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4;
x_31 = lean_st_mk_ref(x_30, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_32);
x_35 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_27, x_34, x_32, x_12, x_13, x_14, x_15, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_15, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_32, x_38);
lean_dec(x_32);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_43 = lean_array_push(x_42, x_3);
x_44 = l_Array_append___rarg(x_43, x_2);
x_45 = lean_array_get_size(x_11);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = x_11;
lean_inc(x_48);
x_49 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(x_46, x_47, x_48);
x_50 = x_49;
x_51 = l_Array_append___rarg(x_44, x_50);
x_52 = 0;
x_53 = 1;
lean_inc(x_12);
lean_inc(x_51);
x_54 = l_Lean_Meta_mkForallFVars(x_51, x_1, x_52, x_53, x_12, x_13, x_14, x_15, x_41);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_12);
x_57 = l_Lean_Meta_mkLambdaFVars(x_51, x_21, x_52, x_53, x_12, x_13, x_14, x_15, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_80 = lean_st_ref_get(x_15, x_59);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 3);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get_uint8(x_82, sizeof(void*)*1);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_60 = x_52;
x_61 = x_84;
goto block_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
lean_inc(x_8);
x_86 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_8, x_12, x_13, x_14, x_15, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_unbox(x_87);
lean_dec(x_87);
x_60 = x_89;
x_61 = x_88;
goto block_79;
}
block_79:
{
if (x_60 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2;
x_63 = lean_box(0);
x_64 = l_Lean_Meta_Match_mkMatcher___lambda__4(x_4, x_55, x_58, x_5, x_6, x_7, x_62, x_40, x_24, x_8, x_46, x_47, x_48, x_9, x_63, x_12, x_13, x_14, x_15, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_58);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_58);
x_66 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__8;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_55);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_55);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_8);
x_74 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_8, x_73, x_12, x_13, x_14, x_15, x_61);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2;
x_78 = l_Lean_Meta_Match_mkMatcher___lambda__4(x_4, x_55, x_58, x_5, x_6, x_7, x_77, x_40, x_24, x_8, x_46, x_47, x_48, x_9, x_75, x_12, x_13, x_14, x_15, x_76);
return x_78;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_55);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = !lean_is_exclusive(x_57);
if (x_90 == 0)
{
return x_57;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_57, 0);
x_92 = lean_ctor_get(x_57, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_57);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_54);
if (x_94 == 0)
{
return x_54;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_54, 0);
x_96 = lean_ctor_get(x_54, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_54);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_35);
if (x_98 == 0)
{
return x_35;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_35, 0);
x_100 = lean_ctor_get(x_35, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_35);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__5), 16, 9);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_7);
lean_closure_set(x_16, 7, x_8);
lean_closure_set(x_16, 8, x_9);
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(x_3, x_7, x_16, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("target: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_mkAppN(x_1, x_2);
x_30 = lean_st_ref_get(x_13, x_14);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = 0;
x_16 = x_35;
x_17 = x_34;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_7);
x_37 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_7, x_10, x_11, x_12, x_13, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
x_16 = x_40;
x_17 = x_39;
goto block_29;
}
block_29:
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Meta_Match_mkMatcher___lambda__6(x_15, x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_15);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_21 = l_Lean_Meta_Match_mkMatcher___lambda__7___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_7);
x_25 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_7, x_24, x_10, x_11, x_12, x_13, x_17);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Match_mkMatcher___lambda__6(x_15, x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_26, x_10, x_11, x_12, x_13, x_27);
lean_dec(x_26);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motiveType: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8;
x_29 = lean_st_ref_get(x_12, x_13);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = 0;
x_15 = x_34;
x_16 = x_33;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__2(x_14, x_9, x_10, x_11, x_12, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_37);
lean_dec(x_37);
x_15 = x_39;
x_16 = x_38;
goto block_28;
}
block_28:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Match_mkMatcher___lambda__7(x_8, x_1, x_2, x_3, x_4, x_5, x_14, x_6, x_17, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_7);
x_20 = l_Lean_Meta_Match_mkMatcher___lambda__8___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___spec__1(x_14, x_23, x_9, x_10, x_11, x_12, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Match_mkMatcher___lambda__7(x_8, x_1, x_2, x_3, x_4, x_5, x_14, x_6, x_25, x_9, x_10, x_11, x_12, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_mkMatcher___lambda__9___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_6);
x_12 = l_Lean_mkSort(x_6);
x_13 = 0;
x_14 = 1;
lean_inc(x_7);
lean_inc(x_1);
x_15 = l_Lean_Meta_mkForallFVars(x_1, x_12, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__8), 13, 7);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_16);
x_19 = l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2;
x_20 = 0;
x_21 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_19, x_20, x_16, x_18, x_7, x_8, x_9, x_10, x_17);
return x_21;
}
else
{
uint8_t x_22; 
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
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_6, x_7, x_8, x_9, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Match_mkMatcher___lambda__9(x_4, x_2, x_14, x_1, x_3, x_19, x_6, x_7, x_8, x_9, x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Match_mkMatcher___lambda__9(x_4, x_2, x_14, x_1, x_3, x_16, x_6, x_7, x_8, x_9, x_15);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__10), 10, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_9);
x_13 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_8, x_11, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Match_mkMatcher___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Match_mkMatcher___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___boxed(lean_object** _args) {
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
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_21 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_22 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
_start:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_22 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_23 = l_Lean_Meta_Match_mkMatcher___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_22, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Match_mkMatcher___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
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
lean_inc(x_1);
x_11 = l_Lean_LocalContext_getFVar_x21(x_1, x_10);
lean_dec(x_10);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_array_set(x_3, x_4, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_2 = x_10;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_1);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = x_1;
x_21 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2(x_16, x_18, x_19, x_20);
x_22 = x_21;
x_23 = lean_array_get_size(x_3);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = x_3;
x_26 = lean_box_usize(x_24);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3___boxed__const__1;
x_28 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2___boxed), 8, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_25);
x_29 = x_28;
x_30 = lean_apply_5(x_29, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_array_to_list(lean_box(0), x_22);
x_34 = lean_array_to_list(lean_box(0), x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_array_to_list(lean_box(0), x_22);
x_40 = lean_array_to_list(lean_box(0), x_37);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
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
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Lean_Expr_fvarId_x21(x_12);
lean_inc(x_1);
x_14 = l_Lean_Meta_dependsOn(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = x_3 + x_18;
x_3 = x_19;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_array_push(x_5, x_12);
x_23 = 1;
x_24 = x_3 + x_23;
x_3 = x_24;
x_5 = x_22;
x_10 = x_21;
goto _start;
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
x_11 = x_20;
x_12 = x_7;
goto block_19;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_8, x_8);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_1);
x_22 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
x_11 = x_22;
x_12 = x_7;
goto block_19;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_25 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
lean_inc(x_2);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4(x_2, x_1, x_23, x_24, x_25, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_11 = x_27;
x_12 = x_28;
goto block_19;
}
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Expr_getAppNumArgsAux(x_2, x_9);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3(x_11, x_2, x_15, x_17, x_3, x_4, x_5, x_6, x_12);
return x_18;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = lean_infer_type(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_17, x_19, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_2 + x_23;
x_25 = x_21;
x_26 = lean_array_uset(x_14, x_2, x_25);
x_2 = x_24;
x_3 = x_26;
x_8 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = x_1;
x_11 = lean_box_usize(x_9);
x_12 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed__const__1;
x_13 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
x_14 = x_13;
x_15 = lean_apply_5(x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_11, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1;
x_18 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_13, x_16, x_17, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_array_to_list(lean_box(0), x_20);
x_22 = lean_array_get_size(x_1);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_array_to_list(lean_box(0), x_24);
x_27 = lean_array_get_size(x_1);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
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
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2;
x_2 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__3;
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4;
x_9 = 0;
x_10 = 1;
x_11 = l_Lean_Meta_mkForallFVars(x_1, x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2;
x_12 = l_Lean_mkConst(x_11, x_10);
x_13 = 0;
x_14 = 1;
x_15 = l_Lean_Meta_mkForallFVars(x_2, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not a matcher: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_getMkMatcherInputInContext___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 7);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_7);
x_12 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1(x_19, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_7);
x_24 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_7, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_ConstantInfo_type(x_25);
x_28 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_29 = lean_array_push(x_28, x_9);
x_30 = l_Array_append___rarg(x_8, x_29);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_30, x_31, x_27, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_30);
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
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
lean_ctor_set(x_13, 0, x_36);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
x_37 = l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_33);
x_38 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_33, x_13, x_37, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2(x_10, x_33, x_11, x_7, x_39, x_2, x_3, x_4, x_5, x_40);
lean_dec(x_11);
lean_dec(x_10);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
lean_dec(x_35);
x_47 = l_Lean_ConstantInfo_levelParams(x_25);
lean_dec(x_25);
x_48 = l_List_redLength___rarg(x_47);
x_49 = lean_mk_empty_array_with_capacity(x_48);
lean_dec(x_48);
x_50 = l_List_toArrayAux___rarg(x_47, x_49);
x_51 = l_Lean_instInhabitedName;
x_52 = lean_array_get(x_51, x_50, x_46);
lean_dec(x_46);
lean_dec(x_50);
x_53 = l_Lean_mkLevelParam(x_52);
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4___boxed), 8, 1);
lean_closure_set(x_54, 0, x_53);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_33);
x_55 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_33, x_13, x_54, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2(x_10, x_33, x_11, x_7, x_56, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_11);
lean_dec(x_10);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_25);
lean_free_object(x_13);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
return x_32;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_32, 0);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_32);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_free_object(x_13);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_24);
if (x_67 == 0)
{
return x_24;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_24, 0);
x_69 = lean_ctor_get(x_24, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_24);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_13, 0);
lean_inc(x_71);
lean_dec(x_13);
lean_inc(x_7);
x_72 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_7, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_ConstantInfo_type(x_73);
x_76 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_77 = lean_array_push(x_76, x_9);
x_78 = l_Array_append___rarg(x_8, x_77);
x_79 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_80 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_78, x_79, x_75, x_2, x_3, x_4, x_5, x_74);
lean_dec(x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_71, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_71, 1);
lean_inc(x_84);
lean_dec(x_71);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_73);
x_86 = l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_81);
x_87 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_81, x_85, x_86, x_2, x_3, x_4, x_5, x_82);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2(x_10, x_81, x_11, x_7, x_88, x_2, x_3, x_4, x_5, x_89);
lean_dec(x_11);
lean_dec(x_10);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_81);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_93 = x_87;
} else {
 lean_dec_ref(x_87);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
lean_dec(x_83);
x_96 = l_Lean_ConstantInfo_levelParams(x_73);
lean_dec(x_73);
x_97 = l_List_redLength___rarg(x_96);
x_98 = lean_mk_empty_array_with_capacity(x_97);
lean_dec(x_97);
x_99 = l_List_toArrayAux___rarg(x_96, x_98);
x_100 = l_Lean_instInhabitedName;
x_101 = lean_array_get(x_100, x_99, x_95);
lean_dec(x_95);
lean_dec(x_99);
x_102 = l_Lean_mkLevelParam(x_101);
x_103 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4___boxed), 8, 1);
lean_closure_set(x_103, 0, x_102);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_81);
x_104 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_81, x_85, x_103, x_2, x_3, x_4, x_5, x_82);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2(x_10, x_81, x_11, x_7, x_105, x_2, x_3, x_4, x_5, x_106);
lean_dec(x_11);
lean_dec(x_10);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_81);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_ctor_get(x_80, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_80, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_114 = x_80;
} else {
 lean_dec_ref(x_80);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_71);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_72, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_72, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_118 = x_72;
} else {
 lean_dec_ref(x_72);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux(x_1, x_22);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_25, x_27);
x_29 = lean_array_get_size(x_28);
x_30 = l_Lean_Meta_Match_MatcherInfo_arity(x_21);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_32 = l_List_redLength___rarg(x_9);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_34 = l_List_toArrayAux___rarg(x_9, x_33);
x_35 = lean_ctor_get(x_21, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
lean_inc(x_36);
lean_inc(x_28);
x_37 = l_Array_extract___rarg(x_28, x_22, x_36);
x_38 = l_Lean_instInhabitedExpr;
x_39 = lean_array_get(x_38, x_28, x_36);
x_40 = lean_nat_add(x_36, x_26);
lean_dec(x_36);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_inc(x_42);
lean_inc(x_28);
x_43 = l_Array_toSubarray___rarg(x_28, x_40, x_42);
x_44 = l_Array_ofSubarray___rarg(x_43);
x_45 = lean_ctor_get(x_21, 2);
lean_inc(x_45);
x_46 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_21);
lean_dec(x_21);
x_47 = lean_nat_add(x_42, x_46);
lean_dec(x_46);
lean_inc(x_47);
lean_inc(x_28);
x_48 = l_Array_toSubarray___rarg(x_28, x_42, x_47);
x_49 = l_Array_ofSubarray___rarg(x_48);
x_50 = l_Array_toSubarray___rarg(x_28, x_47, x_29);
x_51 = l_Array_ofSubarray___rarg(x_50);
x_52 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_52, 0, x_8);
lean_ctor_set(x_52, 1, x_34);
lean_ctor_set(x_52, 2, x_35);
lean_ctor_set(x_52, 3, x_37);
lean_ctor_set(x_52, 4, x_39);
lean_ctor_set(x_52, 5, x_44);
lean_ctor_set(x_52, 6, x_45);
lean_ctor_set(x_52, 7, x_49);
lean_ctor_set(x_52, 8, x_51);
lean_ctor_set(x_11, 0, x_52);
return x_10;
}
else
{
lean_object* x_53; 
lean_dec(x_29);
lean_dec(x_28);
lean_free_object(x_11);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
x_53 = lean_box(0);
lean_ctor_set(x_10, 0, x_53);
return x_10;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_54 = lean_ctor_get(x_11, 0);
lean_inc(x_54);
lean_dec(x_11);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Expr_getAppNumArgsAux(x_1, x_55);
x_57 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1;
lean_inc(x_56);
x_58 = lean_mk_array(x_56, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_56, x_59);
lean_dec(x_56);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_58, x_60);
x_62 = lean_array_get_size(x_61);
x_63 = l_Lean_Meta_Match_MatcherInfo_arity(x_54);
x_64 = lean_nat_dec_lt(x_62, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_65 = l_List_redLength___rarg(x_9);
x_66 = lean_mk_empty_array_with_capacity(x_65);
lean_dec(x_65);
x_67 = l_List_toArrayAux___rarg(x_9, x_66);
x_68 = lean_ctor_get(x_54, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_54, 0);
lean_inc(x_69);
lean_inc(x_69);
lean_inc(x_61);
x_70 = l_Array_extract___rarg(x_61, x_55, x_69);
x_71 = l_Lean_instInhabitedExpr;
x_72 = lean_array_get(x_71, x_61, x_69);
x_73 = lean_nat_add(x_69, x_59);
lean_dec(x_69);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
x_75 = lean_nat_add(x_73, x_74);
lean_dec(x_74);
lean_inc(x_75);
lean_inc(x_61);
x_76 = l_Array_toSubarray___rarg(x_61, x_73, x_75);
x_77 = l_Array_ofSubarray___rarg(x_76);
x_78 = lean_ctor_get(x_54, 2);
lean_inc(x_78);
x_79 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_54);
lean_dec(x_54);
x_80 = lean_nat_add(x_75, x_79);
lean_dec(x_79);
lean_inc(x_80);
lean_inc(x_61);
x_81 = l_Array_toSubarray___rarg(x_61, x_75, x_80);
x_82 = l_Array_ofSubarray___rarg(x_81);
x_83 = l_Array_toSubarray___rarg(x_61, x_80, x_62);
x_84 = l_Array_ofSubarray___rarg(x_83);
x_85 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_67);
lean_ctor_set(x_85, 2, x_68);
lean_ctor_set(x_85, 3, x_70);
lean_ctor_set(x_85, 4, x_72);
lean_ctor_set(x_85, 5, x_77);
lean_ctor_set(x_85, 6, x_78);
lean_ctor_set(x_85, 7, x_82);
lean_ctor_set(x_85, 8, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_10, 0, x_86);
return x_10;
}
else
{
lean_object* x_87; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
x_87 = lean_box(0);
lean_ctor_set(x_10, 0, x_87);
return x_10;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_88 = lean_ctor_get(x_10, 1);
lean_inc(x_88);
lean_dec(x_10);
x_89 = lean_ctor_get(x_11, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_90 = x_11;
} else {
 lean_dec_ref(x_11);
 x_90 = lean_box(0);
}
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Lean_Expr_getAppNumArgsAux(x_1, x_91);
x_93 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1;
lean_inc(x_92);
x_94 = lean_mk_array(x_92, x_93);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_sub(x_92, x_95);
lean_dec(x_92);
x_97 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_94, x_96);
x_98 = lean_array_get_size(x_97);
x_99 = l_Lean_Meta_Match_MatcherInfo_arity(x_89);
x_100 = lean_nat_dec_lt(x_98, x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_101 = l_List_redLength___rarg(x_9);
x_102 = lean_mk_empty_array_with_capacity(x_101);
lean_dec(x_101);
x_103 = l_List_toArrayAux___rarg(x_9, x_102);
x_104 = lean_ctor_get(x_89, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_89, 0);
lean_inc(x_105);
lean_inc(x_105);
lean_inc(x_97);
x_106 = l_Array_extract___rarg(x_97, x_91, x_105);
x_107 = l_Lean_instInhabitedExpr;
x_108 = lean_array_get(x_107, x_97, x_105);
x_109 = lean_nat_add(x_105, x_95);
lean_dec(x_105);
x_110 = lean_ctor_get(x_89, 1);
lean_inc(x_110);
x_111 = lean_nat_add(x_109, x_110);
lean_dec(x_110);
lean_inc(x_111);
lean_inc(x_97);
x_112 = l_Array_toSubarray___rarg(x_97, x_109, x_111);
x_113 = l_Array_ofSubarray___rarg(x_112);
x_114 = lean_ctor_get(x_89, 2);
lean_inc(x_114);
x_115 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_89);
lean_dec(x_89);
x_116 = lean_nat_add(x_111, x_115);
lean_dec(x_115);
lean_inc(x_116);
lean_inc(x_97);
x_117 = l_Array_toSubarray___rarg(x_97, x_111, x_116);
x_118 = l_Array_ofSubarray___rarg(x_117);
x_119 = l_Array_toSubarray___rarg(x_97, x_116, x_98);
x_120 = l_Array_ofSubarray___rarg(x_119);
x_121 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_121, 0, x_8);
lean_ctor_set(x_121, 1, x_103);
lean_ctor_set(x_121, 2, x_104);
lean_ctor_set(x_121, 3, x_106);
lean_ctor_set(x_121, 4, x_108);
lean_ctor_set(x_121, 5, x_113);
lean_ctor_set(x_121, 6, x_114);
lean_ctor_set(x_121, 7, x_118);
lean_ctor_set(x_121, 8, x_120);
if (lean_is_scalar(x_90)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_90;
}
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_88);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_9);
lean_dec(x_8);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_88);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_7);
lean_dec(x_1);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_6);
return x_127;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not a matcher app: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l_Lean_ConstantInfo_name(x_1);
lean_dec(x_1);
x_11 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_addInstance___spec__1(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkAppN(x_12, x_3);
lean_inc(x_14);
x_15 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2(x_14, x_5, x_6, x_7, x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg(x_22, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lean_Meta_Match_getMkMatcherInputInContext(x_25, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_apply_6(x_2, x_27, x_5, x_6, x_7, x_8, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg(x_15, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_ConstantInfo_type(x_21);
x_24 = l_Lean_Meta_Match_MatcherInfo_arity(x_19);
lean_dec(x_19);
lean_ctor_set(x_9, 0, x_24);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1), 9, 2);
lean_closure_set(x_25, 0, x_21);
lean_closure_set(x_25, 1, x_2);
x_26 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_23, x_9, x_25, x_3, x_4, x_5, x_6, x_22);
return x_26;
}
else
{
uint8_t x_27; 
lean_free_object(x_9);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_dec(x_9);
x_32 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_ConstantInfo_type(x_33);
x_36 = l_Lean_Meta_Match_MatcherInfo_arity(x_31);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1), 9, 2);
lean_closure_set(x_38, 0, x_33);
lean_closure_set(x_38, 1, x_2);
x_39 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_35, x_37, x_38, x_3, x_4, x_5, x_6, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_42 = x_32;
} else {
 lean_dec_ref(x_32);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_withMkMatcherInput___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = 1;
lean_inc(x_5);
x_12 = l_Lean_Meta_mkLambdaFVars(x_3, x_1, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_mkLambdaFVars(x_2, x_13, x_10, x_11, x_5, x_6, x_7, x_8, x_14);
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
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1___boxed), 9, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
x_11 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_2, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_15 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2;
x_16 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_15, x_4, x_5, x_6, x_7, x_14);
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = l_Lean_Meta_whnfD(x_1, x_5, x_6, x_7, x_8, x_9);
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
x_24 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_reduceMatcher_x3f___spec__3___rarg(x_20, x_22, x_23, x_5, x_6, x_7, x_8, x_19);
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
x_39 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_Meta_kabstract(x_4, x_17, x_18, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = lean_infer_type(x_1, x_10, x_11, x_12, x_13, x_14);
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
x_27 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_28 = lean_array_push(x_27, x_3);
x_29 = lean_ctor_get(x_2, 8);
lean_inc(x_29);
lean_dec(x_2);
x_30 = l_Array_append___rarg(x_28, x_29);
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
x_37 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_38 = lean_array_push(x_37, x_3);
x_39 = lean_ctor_get(x_2, 8);
lean_inc(x_39);
lean_dec(x_2);
x_40 = l_Array_append___rarg(x_38, x_39);
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = 1;
lean_inc(x_7);
x_14 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_inc(x_6);
x_18 = lean_array_to_list(lean_box(0), x_6);
lean_inc(x_17);
x_19 = l_Lean_mkConst(x_17, x_18);
x_20 = lean_ctor_get(x_3, 3);
lean_inc(x_20);
lean_inc(x_20);
x_21 = l_Lean_mkAppN(x_19, x_20);
lean_inc(x_15);
x_22 = l_Lean_mkApp(x_21, x_15);
lean_inc(x_4);
x_23 = l_Lean_mkAppN(x_22, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
x_24 = l_Lean_Meta_check(x_23, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
x_26 = l_Lean_Meta_isTypeCorrect(x_23, x_7, x_8, x_9, x_10, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2;
x_31 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_30, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_box(0);
x_38 = l_Lean_Meta_MatcherApp_addArg___lambda__1(x_23, x_3, x_5, x_17, x_6, x_20, x_15, x_4, x_37, x_7, x_8, x_9, x_10, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
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
x_16 = l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1(x_2, x_3, x_15, x_12, x_6, x_7, x_8, x_9, x_13);
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
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" arguments");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Nat_repr(x_12);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_20, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_12);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_MatcherApp_addArg___lambda__3(x_1, x_2, x_3, x_4, x_26, x_5, x_6, x_7, x_8, x_9);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lambda__4), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_MatcherApp_addArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_9460_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8;
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
lean_object* initialize_Lean_Meta_Tactic_Contradiction(lean_object*);
lean_object* initialize_Lean_Meta_GeneralizeTelescope(lean_object*);
lean_object* initialize_Lean_Meta_Match_Basic(lean_object*);
lean_object* initialize_Lean_Meta_Match_MVarRenaming(lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseValues(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Match(lean_object* w) {
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
res = initialize_Lean_Meta_Tactic_Contradiction(lean_io_mk_world());
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
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5);
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
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__9 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__9);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__11 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__11);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1);
l_Lean_Meta_Match_State_used___default___closed__1 = _init_l_Lean_Meta_Match_State_used___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_State_used___default___closed__1);
l_Lean_Meta_Match_State_used___default = _init_l_Lean_Meta_Match_State_used___default();
lean_mark_persistent(l_Lean_Meta_Match_State_used___default);
l_Lean_Meta_Match_State_counterExamples___default = _init_l_Lean_Meta_Match_State_counterExamples___default();
lean_mark_persistent(l_Lean_Meta_Match_State_counterExamples___default);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__1);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__2);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__3);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1);
l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__1 = _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__1);
l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2 = _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2);
l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__3 = _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__3();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__3);
l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4 = _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4);
l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__5 = _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__5();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__5);
l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6 = _init_l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__5 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__5);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__3);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__1);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__4);
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
l_Lean_Meta_Match_Unify_assign___closed__7 = _init_l_Lean_Meta_Match_Unify_assign___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__7);
l_Lean_Meta_Match_Unify_assign___closed__8 = _init_l_Lean_Meta_Match_Unify_assign___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__8);
l_Lean_Meta_Match_Unify_assign___closed__9 = _init_l_Lean_Meta_Match_Unify_assign___closed__9();
lean_mark_persistent(l_Lean_Meta_Match_Unify_assign___closed__9);
l_Lean_Meta_Match_Unify_unify___closed__1 = _init_l_Lean_Meta_Match_Unify_unify___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_Unify_unify___closed__1);
l_Lean_Meta_Match_Unify_unify___closed__2 = _init_l_Lean_Meta_Match_Unify_unify___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_Unify_unify___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__6 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__6);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__7 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__7);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__8 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__8);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__9 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__9);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed__const__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1___boxed__const__1);
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
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__5);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__6 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__6);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__7 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__7);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__9 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__9);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__10 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__10);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__12 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__12);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__13 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__13);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__14);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__15 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__15);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__17 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__17);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__1 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__1();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__1);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__2 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__2();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed__const__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___boxed__const__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__3 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__3();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__3);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__5 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__5();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__5);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__2);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__3 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__3();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__3);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__5 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__5();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__5);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__6 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__6();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__6);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2);
l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1);
l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__2);
l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__3 = _init_l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__2___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__4___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___lambda__1___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__4);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__1 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__1();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__1);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__2 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__2();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__2);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__3 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__3();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__3);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__4 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__4();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__4);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__5 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__5();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__5);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__6 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__6();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259____closed__6);
l_Lean_Meta_Match_bootstrap_genMatcherCode___closed__1 = _init_l_Lean_Meta_Match_bootstrap_genMatcherCode___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_bootstrap_genMatcherCode___closed__1);
res = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7259_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Match_bootstrap_genMatcherCode = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Match_bootstrap_genMatcherCode);
lean_dec_ref(res);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__1 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__1();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__1);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__2 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__2();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__2);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__3);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__4 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__4();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__4);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__5);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__6 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__6();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__6);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__7 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__7();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__7);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__8 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__8();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__8);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__9 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__9();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282____closed__9);
l_Lean_Meta_Match_matcherExt___closed__1 = _init_l_Lean_Meta_Match_matcherExt___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_matcherExt___closed__1);
l_Lean_Meta_Match_matcherExt___closed__2 = _init_l_Lean_Meta_Match_matcherExt___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_matcherExt___closed__2);
res = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_7282_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Match_matcherExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Match_matcherExt);
lean_dec_ref(res);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__3 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__3();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__3);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__4 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__4();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1___closed__4);
l_Lean_Meta_Match_mkMatcherAuxDefinition___closed__1 = _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcherAuxDefinition___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__3___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2);
l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3 = _init_l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3);
l_Lean_Meta_Match_mkMatcher___lambda__4___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__4___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2);
l_Lean_Meta_Match_mkMatcher___lambda__4___closed__3 = _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__4___closed__3);
l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4 = _init_l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__7 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__7);
l_Lean_Meta_Match_mkMatcher___lambda__5___closed__8 = _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__5___closed__8);
l_Lean_Meta_Match_mkMatcher___lambda__7___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__7___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__7___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__7___closed__2);
l_Lean_Meta_Match_mkMatcher___lambda__8___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__8___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__8___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__8___closed__2);
l_Lean_Meta_Match_mkMatcher___lambda__9___closed__1 = _init_l_Lean_Meta_Match_mkMatcher___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__9___closed__1);
l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2 = _init_l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3___boxed__const__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1);
l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed__const__1 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1___boxed__const__1);
l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1);
l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__1 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__1);
l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2);
l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__3 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__3);
l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4);
l_Lean_Meta_Match_getMkMatcherInputInContext___closed__1 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___closed__1);
l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2);
l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3 = _init_l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3);
l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__1);
l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__2 = _init_l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2);
l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1);
l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2);
l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1);
l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2);
l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__3 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__3);
l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__4 = _init_l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__4);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_9460_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
