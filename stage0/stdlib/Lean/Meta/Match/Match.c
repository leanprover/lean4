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
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__5;
lean_object* l_Lean_Meta_Match_Example_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__13;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__3;
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_List_get___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__1(lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___boxed(lean_object**);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__5;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__4;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__7;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_isAltVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__2;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__1;
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5;
lean_object* l_Lean_Meta_dependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Unify_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__6;
extern lean_object* l_Lean_Meta_Match_instInhabitedAlt;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3;
extern lean_object* l_instInhabitedNat;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__9___closed__1;
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___boxed(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2___boxed(lean_object**);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__3;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__2;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Match_Unify_assign___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__13;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar___boxed(lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__4;
lean_object* l_Std_AssocList_toList___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls(lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getInductiveVal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4;
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___closed__1;
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_State_fvarSubst___default;
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__9;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__4;
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__4;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__4;
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
static lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__2;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__6___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__7(lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2;
uint8_t l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__3;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____lambda__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_12053_(lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__7___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasVarPattern(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4___closed__3;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1(uint8_t, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__16;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashSet___at_Lean_Meta_Match_State_used___default___spec__1(lean_object*);
lean_object* l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__2;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__7___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts(lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3(lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___boxed(lean_object**);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_54____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasRecursiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getInductiveUniverseAndParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample(lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__4;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__3;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__6;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput(lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___spec__1(uint8_t, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_matcherExt;
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_State_counterExamples___default;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__2;
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__4;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isFirstPatternVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Unify_occurs___lambda__1(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__8;
static lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__3;
static lean_object* l_Lean_Meta_Match_Unify_unify___closed__1;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___boxed(lean_object**);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Closure_mkValueTypeClosure(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition___spec__1(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__8___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_List_elem___at_Lean_Occurrences_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___closed__1;
lean_object* l_Lean_mkSimpleThunkType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__2;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_Match_Unify_assign___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNonTrivialExample___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__1;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__8___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__2;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__6;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_isCurrVarInductive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_Match_instInhabitedPattern;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1;
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__8;
lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__6;
lean_object* l_Lean_Meta_Match_Problem_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_unify___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasCtorPattern___boxed(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___boxed(lean_object**);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_assignGoalOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_replaceFVarId(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern___boxed(lean_object*);
static lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasValPattern___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__2;
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__2;
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2;
LEAN_EXPORT lean_object* l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNumPatterns___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__10;
LEAN_EXPORT lean_object* l_Array_indexOfAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___boxed(lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_Match_Example_replaceFVarId(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1;
LEAN_EXPORT lean_object* l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__9;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition___spec__1(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Match_Unify_assign___closed__5;
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
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__3___closed__1;
lean_object* l_Lean_Meta_Match_withGoalOf___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSetImp_insert___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Meta_ACLt_lt_lexSameCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_occurs___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__1;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep___closed__2;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__6;
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_examplesToMessageData(lean_object*);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_State_used___default;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_occurs___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__8;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_inLocalDecls___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1;
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Std_HashSetImp_expand___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__4;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__7;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes___spec__1___boxed(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasArrayLitPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableBool___boxed(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__4___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__11;
lean_object* lean_usize_to_nat(size_t);
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
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2;
extern lean_object* l_Lean_Meta_Match_instInhabitedProblem;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search___closed__1;
static lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__1;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern___spec__1(uint8_t, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___spec__1___closed__5;
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Meta_MatcherApp_addArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__2;
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Alt_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__12;
static lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338_(lean_object*);
static lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1;
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition___spec__1(uint8_t, lean_object*);
static lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_isAltVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__4;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwInductiveTypeExpected___rarg___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_expandIfVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Unify_assign___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_withMkMatcherInput___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___closed__1;
static lean_object* l_Lean_Meta_Match_withMkMatcherInput___rarg___lambda__1___closed__2;
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
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_14, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_13, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___spec__1(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkAppN(x_4, x_12);
x_15 = 0;
x_16 = 1;
x_17 = 1;
x_18 = l_Lean_Meta_mkForallFVars(x_5, x_14, x_15, x_16, x_17, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_16 = lean_box_usize(x_15);
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___boxed__const__1;
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1___boxed), 10, 5);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_13);
lean_closure_set(x_18, 3, x_1);
lean_closure_set(x_18, 4, x_2);
x_19 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_9, x_18, x_4, x_5, x_6, x_7, x_8);
return x_19;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType___lambda__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
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
lean_inc(x_15);
x_21 = l_List_mapM___at_Lean_Meta_Match_instantiateAltLHSMVars___spec__1(x_3, x_14, x_15, x_16, x_17, x_18);
if (x_4 == 0)
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__1___closed__5;
x_31 = l_Lean_mkApp(x_13, x_30);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg(x_10, x_11, x_12, x_33, x_20, x_14, x_15, x_16, x_17, x_29);
return x_34;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
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
x_24 = l_Array_mapMUnsafe_map___at_Lean_Meta_Closure_mkBinding___spec__1(x_22, x_23, x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_24);
lean_inc(x_1);
x_25 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_mkMinorType(x_1, x_24, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Array_isEmpty___rarg(x_24);
if (x_28 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_array_get_size(x_24);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_26);
lean_ctor_set(x_70, 1, x_69);
x_29 = x_70;
goto block_68;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = l_Lean_mkSimpleThunkType(x_26);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_29 = x_73;
goto block_68;
}
block_68:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_List_lengthTRAux___rarg(x_4, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_33, x_34);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
x_37 = lean_name_append_index_after(x_36, x_35);
x_38 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__8;
x_57 = lean_st_ref_get(x_9, x_27);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = 0;
x_39 = x_62;
x_40 = x_61;
goto block_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_38, x_6, x_7, x_8, x_9, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_39 = x_67;
x_40 = x_66;
goto block_56;
}
block_56:
{
if (x_39 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(x_31, x_5, x_16, x_28, x_24, x_15, x_33, x_17, x_4, x_1, x_2, x_14, x_37, x_30, x_41, x_6, x_7, x_8, x_9, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_inc(x_37);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_37);
x_44 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__10;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_30);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_30);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_38, x_51, x_6, x_7, x_8, x_9, x_40);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___lambda__2(x_31, x_5, x_16, x_28, x_24, x_15, x_33, x_17, x_4, x_1, x_2, x_14, x_37, x_30, x_53, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_53);
return x_55;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_24);
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
x_74 = !lean_is_exclusive(x_25);
if (x_74 == 0)
{
return x_25;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_25, 0);
x_76 = lean_ctor_get(x_25, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_25);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
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
static lean_object* _init_l_Lean_Meta_Match_State_used___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_instInhabitedProblem;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_instInhabitedAlt;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Match.Match");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processSkipInaccessible");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(142u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4;
x_10 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4;
x_14 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_4, 4);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 0);
lean_dec(x_23);
lean_ctor_set(x_4, 4, x_22);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_18;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_dec(x_5);
lean_ctor_set(x_4, 4, x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_18;
x_2 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
x_30 = lean_ctor_get(x_4, 2);
x_31 = lean_ctor_get(x_4, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_33 = x_5;
} else {
 lean_dec_ref(x_5);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_32);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
x_1 = x_18;
x_2 = x_35;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_5, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_5, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4;
x_42 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_41);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_42);
x_1 = x_40;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4;
x_46 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_2);
x_1 = x_44;
x_2 = x_47;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(138u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___closed__1;
x_4 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__1(x_3);
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
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3(x_6, x_9);
lean_ctor_set(x_1, 2, x_10);
lean_ctor_set(x_1, 1, x_8);
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
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3(x_12, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_13);
return x_17;
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
x_13 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_11);
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
x_10 = lean_uint64_to_usize(x_9);
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
x_20 = lean_uint64_to_usize(x_19);
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
x_8 = lean_uint64_to_usize(x_7);
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
x_17 = lean_uint64_to_usize(x_16);
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
x_8 = lean_uint64_to_usize(x_7);
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
x_24 = lean_uint64_to_usize(x_23);
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
x_4 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_3);
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
static lean_object* _init_l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
x_33 = lean_ctor_get(x_10, 2);
x_34 = lean_ctor_get(x_10, 3);
x_35 = lean_ctor_get(x_10, 4);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_28, 1);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 2);
lean_inc(x_41);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkEqRefl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_ctor_set(x_28, 0, x_40);
lean_inc(x_1);
x_45 = l_Lean_Meta_Match_Alt_replaceFVarId(x_39, x_1, x_10);
x_46 = l_Lean_Meta_Match_Alt_replaceFVarId(x_41, x_43, x_45);
x_13 = x_46;
x_14 = x_44;
goto block_27;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_28);
lean_dec(x_37);
lean_free_object(x_10);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_28, 1);
lean_inc(x_51);
lean_dec(x_28);
x_52 = lean_ctor_get(x_29, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_29, 2);
lean_inc(x_54);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_55 = l_Lean_Meta_mkEqRefl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_10, 4, x_58);
lean_inc(x_1);
x_59 = l_Lean_Meta_Match_Alt_replaceFVarId(x_52, x_1, x_10);
x_60 = l_Lean_Meta_Match_Alt_replaceFVarId(x_54, x_56, x_59);
x_13 = x_60;
x_14 = x_57;
goto block_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_free_object(x_10);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
x_67 = lean_ctor_get(x_10, 2);
x_68 = lean_ctor_get(x_10, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_69 = lean_ctor_get(x_28, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_70 = x_28;
} else {
 lean_dec_ref(x_28);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_29, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_29, 2);
lean_inc(x_73);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_74 = l_Lean_Meta_mkEqRefl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_69);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_66);
lean_ctor_set(x_78, 2, x_67);
lean_ctor_set(x_78, 3, x_68);
lean_ctor_set(x_78, 4, x_77);
lean_inc(x_1);
x_79 = l_Lean_Meta_Match_Alt_replaceFVarId(x_71, x_1, x_78);
x_80 = l_Lean_Meta_Match_Alt_replaceFVarId(x_73, x_75, x_79);
x_13 = x_80;
x_14 = x_76;
goto block_27;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_83 = x_74;
} else {
 lean_dec_ref(x_74);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
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
x_15 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_14);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__2(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1;
x_3 = lean_unsigned_to_nat(160u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2;
x_9 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___lambda__1), 10, 5);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_7);
lean_closure_set(x_14, 4, x_12);
x_15 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_14, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processVariable");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(200u);
x_4 = lean_unsigned_to_nat(40u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
x_29 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(x_29, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_13 = x_31;
x_14 = x_32;
goto block_27;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_37; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
switch (lean_obj_tag(x_37)) {
case 0:
{
uint8_t x_38; 
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_10);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_10, 4);
lean_dec(x_39);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
lean_ctor_set(x_10, 4, x_40);
x_13 = x_10;
x_14 = x_7;
goto block_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
x_43 = lean_ctor_get(x_10, 2);
x_44 = lean_ctor_get(x_10, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_45);
x_13 = x_46;
x_14 = x_7;
goto block_27;
}
}
case 1:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_10, 4);
lean_dec(x_48);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_dec(x_28);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
lean_dec(x_37);
lean_ctor_set(x_10, 4, x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_51 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(x_50, x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_13 = x_52;
x_14 = x_53;
goto block_27;
}
else
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
x_60 = lean_ctor_get(x_10, 2);
x_61 = lean_ctor_get(x_10, 3);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_dec(x_28);
x_63 = lean_ctor_get(x_37, 0);
lean_inc(x_63);
lean_dec(x_37);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_65 = l_Lean_Meta_Match_Alt_checkAndReplaceFVarId(x_63, x_1, x_64, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_13 = x_66;
x_14 = x_67;
goto block_27;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
default: 
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_10);
x_72 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(x_72, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_13 = x_74;
x_14 = x_75;
goto block_27;
}
else
{
uint8_t x_76; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
block_27:
{
lean_object* x_15; 
x_15 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_14);
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
x_11 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(195u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___closed__1;
x_9 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___lambda__1), 10, 5);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_10);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_12);
x_16 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
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
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Match_Unify_occurs___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
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
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_12);
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
x_1 = lean_mk_string("failed to unify");
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
x_1 = lean_mk_string("\nwith");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_5);
x_9 = l_Lean_Meta_instantiateMVars(x_2, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = l_Lean_Meta_instantiateMVars(x_3, x_4, x_5, x_6, x_7, x_11);
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
lean_inc(x_13);
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
lean_dec(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Match_Unify_assign___closed__2;
x_49 = lean_st_ref_get(x_7, x_28);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*1);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = 0;
x_30 = x_54;
x_31 = x_53;
goto block_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_29, x_4, x_5, x_6, x_7, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unbox(x_57);
lean_dec(x_57);
x_30 = x_59;
x_31 = x_58;
goto block_48;
}
block_48:
{
lean_object* x_32; 
x_32 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__1;
if (x_30 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_10);
x_33 = lean_box(0);
x_34 = lean_apply_6(x_32, x_33, x_4, x_5, x_6, x_7, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = l_Lean_indentExpr(x_10);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f___closed__5;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_indentExpr(x_13);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_29, x_43, x_4, x_5, x_6, x_7, x_31);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_apply_6(x_32, x_45, x_4, x_5, x_6, x_7, x_46);
return x_47;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_26);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_26, 0);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_26, 0, x_62);
return x_26;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_26, 0);
x_64 = lean_ctor_get(x_26, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_26);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_21);
if (x_67 == 0)
{
return x_21;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_21, 0);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_21);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
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
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l_Lean_Expr_fvarId_x21(x_11);
lean_inc(x_4);
x_15 = l_Lean_Meta_getLocalDecl(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_13, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_4);
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
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
lean_inc(x_5);
x_12 = l_Lean_mkAppN(x_1, x_5);
lean_inc(x_3);
x_13 = l_Lean_Meta_Match_Alt_replaceFVarId(x_2, x_12, x_3);
x_14 = lean_array_get_size(x_5);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_7);
lean_inc(x_5);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__1(x_15, x_16, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_to_list(lean_box(0), x_18);
x_21 = lean_ctor_get(x_13, 3);
lean_inc(x_21);
x_22 = l_List_appendTR___rarg(x_20, x_21);
lean_inc(x_22);
x_23 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_unify_x3f(x_22, x_6, x_4, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_23, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_box(0);
x_36 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_34, x_22, x_35);
lean_inc(x_34);
x_37 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_34, x_36, x_35);
x_38 = lean_ctor_get(x_13, 4);
lean_inc(x_38);
lean_inc(x_34);
x_39 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_34, x_38, x_35);
x_40 = lean_ctor_get(x_13, 2);
lean_inc(x_40);
lean_dec(x_13);
lean_inc(x_34);
x_41 = l_Lean_Meta_FVarSubst_apply(x_34, x_40);
x_42 = lean_array_to_list(lean_box(0), x_5);
x_43 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_34, x_37, x_42, x_35);
lean_dec(x_34);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_dec(x_3);
x_46 = l_List_appendTR___rarg(x_43, x_39);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_37);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_24, 0, x_47);
return x_23;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_48 = lean_ctor_get(x_24, 0);
lean_inc(x_48);
lean_dec(x_24);
x_49 = lean_box(0);
x_50 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_48, x_22, x_49);
lean_inc(x_48);
x_51 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_48, x_50, x_49);
x_52 = lean_ctor_get(x_13, 4);
lean_inc(x_52);
lean_inc(x_48);
x_53 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_48, x_52, x_49);
x_54 = lean_ctor_get(x_13, 2);
lean_inc(x_54);
lean_dec(x_13);
lean_inc(x_48);
x_55 = l_Lean_Meta_FVarSubst_apply(x_48, x_54);
x_56 = lean_array_to_list(lean_box(0), x_5);
x_57 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_48, x_51, x_56, x_49);
lean_dec(x_48);
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
x_60 = l_List_appendTR___rarg(x_57, x_53);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_51);
lean_ctor_set(x_61, 4, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_23, 0, x_62);
return x_23;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_dec(x_23);
x_64 = lean_ctor_get(x_24, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_65 = x_24;
} else {
 lean_dec_ref(x_24);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
x_67 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__2(x_64, x_22, x_66);
lean_inc(x_64);
x_68 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__3(x_64, x_67, x_66);
x_69 = lean_ctor_get(x_13, 4);
lean_inc(x_69);
lean_inc(x_64);
x_70 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__4(x_64, x_69, x_66);
x_71 = lean_ctor_get(x_13, 2);
lean_inc(x_71);
lean_dec(x_13);
lean_inc(x_64);
x_72 = l_Lean_Meta_FVarSubst_apply(x_64, x_71);
x_73 = lean_array_to_list(lean_box(0), x_5);
x_74 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f___spec__5(x_64, x_68, x_73, x_66);
lean_dec(x_64);
x_75 = lean_ctor_get(x_3, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l_List_appendTR___rarg(x_74, x_70);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_72);
lean_ctor_set(x_78, 3, x_68);
lean_ctor_set(x_78, 4, x_77);
if (lean_is_scalar(x_65)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_65;
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_63);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_23);
if (x_81 == 0)
{
return x_23;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_23, 0);
x_83 = lean_ctor_get(x_23, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_23);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_17);
if (x_85 == 0)
{
return x_17;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_17, 0);
x_87 = lean_ctor_get(x_17, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_17);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_21 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_16);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
x_23 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_2, x_3, x_4, x_22, x_6, x_7);
lean_dec(x_6);
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_26 = l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_4, x_25, x_10, x_11, x_12, x_13, x_18);
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
x_40 = l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__4(x_38, x_39);
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
x_55 = l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__4(x_53, x_54);
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
x_68 = l_Lean_throwErrorAt___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__2(x_4, x_67, x_10, x_11, x_12, x_13, x_60);
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
x_83 = l_List_mapTRAux___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__4(x_81, x_82);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
x_3 = lean_unsigned_to_nat(341u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2;
x_12 = l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_11, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf___closed__3;
x_38 = lean_st_ref_get(x_6, x_15);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = 0;
x_24 = x_43;
x_25 = x_42;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_23, x_3, x_4, x_5, x_6, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_24 = x_48;
x_25 = x_47;
goto block_37;
}
block_37:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(x_21, x_22, x_13, x_16, x_2, x_20, x_17, x_18, x_19, x_26, x_3, x_4, x_5, x_6, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_21);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_21);
x_29 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_23, x_32, x_3, x_4, x_5, x_6, x_25);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Match_processInaccessibleAsCtor___lambda__2(x_21, x_22, x_13, x_16, x_2, x_20, x_17, x_18, x_19, x_34, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_34);
return x_36;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_dec(x_8);
x_50 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__2;
x_51 = l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_50, x_3, x_4, x_5, x_6, x_49);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Match.Match.0.Lean.Meta.Match.processConstructor");
return x_1;
}
}
static lean_object* _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__1;
x_3 = lean_unsigned_to_nat(409u);
x_4 = lean_unsigned_to_nat(48u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_21 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_21, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_13 = x_23;
x_14 = x_24;
goto block_19;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; 
lean_dec(x_29);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_30 = l_Lean_Meta_Match_processInaccessibleAsCtor(x_10, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_13 = x_31;
x_14 = x_32;
goto block_19;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
case 1:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_10, 4);
lean_dec(x_38);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
lean_ctor_set(x_10, 4, x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_41 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(x_10, x_40, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_13 = x_42;
x_14 = x_43;
goto block_19;
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
x_50 = lean_ctor_get(x_10, 2);
x_51 = lean_ctor_get(x_10, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_dec(x_20);
x_53 = lean_ctor_get(x_29, 0);
lean_inc(x_53);
lean_dec(x_29);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set(x_54, 4, x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoCtor_x3f(x_54, x_53, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_13 = x_56;
x_14 = x_57;
goto block_19;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
case 2:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_10);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_10, 4);
lean_dec(x_63);
x_64 = lean_ctor_get(x_20, 1);
lean_inc(x_64);
lean_dec(x_20);
x_65 = lean_ctor_get(x_29, 3);
lean_inc(x_65);
lean_dec(x_29);
x_66 = l_List_appendTR___rarg(x_65, x_64);
lean_ctor_set(x_10, 4, x_66);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_10);
x_13 = x_67;
x_14 = x_8;
goto block_19;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_10, 0);
x_69 = lean_ctor_get(x_10, 1);
x_70 = lean_ctor_get(x_10, 2);
x_71 = lean_ctor_get(x_10, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_10);
x_72 = lean_ctor_get(x_20, 1);
lean_inc(x_72);
lean_dec(x_20);
x_73 = lean_ctor_get(x_29, 3);
lean_inc(x_73);
lean_dec(x_29);
x_74 = l_List_appendTR___rarg(x_73, x_72);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_69);
lean_ctor_set(x_75, 2, x_70);
lean_ctor_set(x_75, 3, x_71);
lean_ctor_set(x_75, 4, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_13 = x_76;
x_14 = x_8;
goto block_19;
}
}
default: 
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_10);
x_77 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_78 = l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_77, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_13 = x_79;
x_14 = x_80;
goto block_19;
}
else
{
uint8_t x_81; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_14 = lean_array_uget(x_6, x_5);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_6, x_5, x_15);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_array_to_list(lean_box(0), x_19);
lean_inc(x_2);
lean_inc(x_21);
x_22 = l_List_appendTR___rarg(x_21, x_2);
x_23 = lean_box(0);
lean_inc(x_20);
x_24 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__4(x_20, x_22, x_23);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__5(x_21, x_23);
lean_inc(x_25);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
x_29 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(x_3, x_27, x_28, x_23);
lean_dec(x_27);
x_30 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_20, x_29, x_23);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(x_25, x_31, x_23);
x_33 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__9(x_20, x_32, x_23);
x_34 = l_List_reverse___rarg(x_33);
lean_inc(x_18);
x_35 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11___lambda__1), 11, 6);
lean_closure_set(x_35, 0, x_25);
lean_closure_set(x_35, 1, x_34);
lean_closure_set(x_35, 2, x_23);
lean_closure_set(x_35, 3, x_18);
lean_closure_set(x_35, 4, x_24);
lean_closure_set(x_35, 5, x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_18, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = 1;
x_40 = lean_usize_add(x_5, x_39);
x_41 = lean_array_uset(x_16, x_5, x_37);
x_5 = x_40;
x_6 = x_41;
x_11 = x_38;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__1;
x_3 = lean_unsigned_to_nat(362u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1;
x_12 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(x_11, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_15);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___boxed), 9, 3);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_1);
x_20 = l_Lean_Expr_fvarId_x21(x_17);
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts___rarg___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_20);
lean_inc(x_14);
lean_inc(x_1);
x_22 = l_Lean_commitWhenSome_x3f___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__2___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__3(x_1, x_19, x_14, x_20, x_21, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_1, 3);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
lean_ctor_set(x_1, 1, x_18);
x_31 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_32 = lean_array_push(x_31, x_1);
lean_ctor_set(x_22, 0, x_32);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_18);
x_34 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_35 = lean_array_push(x_34, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_38 = x_22;
} else {
 lean_dec_ref(x_22);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_18);
lean_ctor_set(x_39, 2, x_15);
lean_ctor_set(x_39, 3, x_16);
x_40 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2;
x_41 = lean_array_push(x_40, x_39);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_dec(x_22);
x_44 = lean_ctor_get(x_23, 0);
lean_inc(x_44);
lean_dec(x_23);
x_45 = lean_array_get_size(x_44);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11(x_1, x_18, x_20, x_46, x_47, x_44, x_3, x_4, x_5, x_6, x_43);
lean_dec(x_20);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_22);
if (x_49 == 0)
{
return x_22;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_22, 0);
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_22);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
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
x_25 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_7, x_2, x_3, x_4, x_5, x_24);
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
x_13 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_7, x_12, x_2, x_3, x_4, x_5, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2(x_1, x_14, x_2, x_3, x_4, x_5, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__11(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(439u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_21 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_21, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_13 = x_23;
x_14 = x_24;
goto block_19;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
x_33 = lean_ctor_get(x_10, 2);
x_34 = lean_ctor_get(x_10, 3);
x_35 = lean_ctor_get(x_10, 4);
lean_dec(x_35);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_38 = l_Lean_Meta_isExprDefEq(x_1, x_37, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_free_object(x_10);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_13 = x_42;
x_14 = x_41;
goto block_19;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
lean_ctor_set(x_10, 4, x_36);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_10);
x_13 = x_44;
x_14 = x_43;
goto block_19;
}
}
else
{
uint8_t x_45; 
lean_dec(x_36);
lean_free_object(x_10);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 1);
x_51 = lean_ctor_get(x_10, 2);
x_52 = lean_ctor_get(x_10, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_dec(x_20);
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
lean_dec(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_55 = l_Lean_Meta_isExprDefEq(x_1, x_54, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_box(0);
x_13 = x_59;
x_14 = x_58;
goto block_19;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_51);
lean_ctor_set(x_61, 3, x_52);
lean_ctor_set(x_61, 4, x_53);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_13 = x_62;
x_14 = x_60;
goto block_19;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_67 = l_Lean_Meta_Match_Pattern_toMessageData(x_29);
x_68 = l_Lean_indentD(x_67);
x_69 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__4;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__6;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_indentExpr(x_1);
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_76, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(428u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_21 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_panic___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__1(x_21, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_13 = x_23;
x_14 = x_24;
goto block_19;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_20);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_32 = l_Lean_Meta_Match_processInaccessibleAsCtor(x_10, x_31, x_4, x_5, x_6, x_7, x_8);
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
case 2:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
x_42 = lean_ctor_get(x_10, 2);
x_43 = lean_ctor_get(x_10, 3);
x_44 = lean_ctor_get(x_10, 4);
lean_dec(x_44);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_dec(x_20);
x_46 = lean_ctor_get(x_29, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 3);
lean_inc(x_47);
lean_dec(x_29);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_name_eq(x_46, x_49);
lean_dec(x_49);
lean_dec(x_46);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_45);
lean_free_object(x_10);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_51 = lean_box(0);
x_13 = x_51;
x_14 = x_8;
goto block_19;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_List_appendTR___rarg(x_47, x_45);
lean_ctor_set(x_10, 4, x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_10);
x_13 = x_53;
x_14 = x_8;
goto block_19;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_10, 1);
x_56 = lean_ctor_get(x_10, 2);
x_57 = lean_ctor_get(x_10, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_10);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_dec(x_20);
x_59 = lean_ctor_get(x_29, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_29, 3);
lean_inc(x_60);
lean_dec(x_29);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_name_eq(x_59, x_62);
lean_dec(x_62);
lean_dec(x_59);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
x_64 = lean_box(0);
x_13 = x_64;
x_14 = x_8;
goto block_19;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l_List_appendTR___rarg(x_60, x_58);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_55);
lean_ctor_set(x_66, 2, x_56);
lean_ctor_set(x_66, 3, x_57);
lean_ctor_set(x_66, 4, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_13 = x_67;
x_14 = x_8;
goto block_19;
}
}
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_68 = l_Lean_Meta_Match_Pattern_toMessageData(x_29);
x_69 = l_Lean_indentD(x_68);
x_70 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__2___closed__3;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwError___at_Lean_Meta_Match_processInaccessibleAsCtor___spec__3(x_73, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(414u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___closed__1;
x_9 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable___lambda__1), 10, 5);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_10);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_12);
x_16 = l_Lean_Meta_Match_withGoalOf___rarg(x_1, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
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
x_10 = l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(x_1, x_9);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; 
lean_dec(x_8);
x_13 = l_List_reverse___rarg(x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_8);
x_17 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_8, x_15);
lean_ctor_set(x_11, 1, x_12);
lean_ctor_set(x_11, 0, x_17);
{
lean_object* _tmp_6 = lean_box(0);
lean_object* _tmp_10 = x_16;
lean_object* _tmp_11 = x_11;
x_7 = _tmp_6;
x_11 = _tmp_10;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
lean_inc(x_8);
x_21 = l_Lean_Meta_Match_Alt_applyFVarSubst(x_8, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
x_7 = lean_box(0);
x_11 = x_20;
x_12 = x_22;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
x_3 = lean_unsigned_to_nat(479u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = l_List_reverse___rarg(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_21 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_20);
lean_ctor_set(x_12, 1, x_13);
lean_ctor_set(x_12, 0, x_21);
{
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_11 = x_18;
lean_object* _tmp_12 = x_12;
x_8 = _tmp_7;
x_12 = _tmp_11;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_25 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_8 = lean_box(0);
x_12 = x_23;
x_13 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
switch (lean_obj_tag(x_28)) {
case 1:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_15, 4);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_16, 1);
x_34 = lean_ctor_get(x_16, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
lean_ctor_set(x_15, 4, x_33);
lean_inc(x_9);
x_36 = l_Lean_Meta_Match_Alt_replaceFVarId(x_35, x_9, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 0, x_36);
x_8 = lean_box(0);
x_12 = x_29;
x_13 = x_16;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
lean_ctor_set(x_15, 4, x_38);
lean_inc(x_9);
x_40 = l_Lean_Meta_Match_Alt_replaceFVarId(x_39, x_9, x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_13);
x_8 = lean_box(0);
x_12 = x_29;
x_13 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
x_45 = lean_ctor_get(x_15, 2);
x_46 = lean_ctor_get(x_15, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_48 = x_16;
} else {
 lean_dec_ref(x_16);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_28, 0);
lean_inc(x_49);
lean_dec(x_28);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_45);
lean_ctor_set(x_50, 3, x_46);
lean_ctor_set(x_50, 4, x_47);
lean_inc(x_9);
x_51 = l_Lean_Meta_Match_Alt_replaceFVarId(x_49, x_9, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_13);
x_8 = lean_box(0);
x_12 = x_29;
x_13 = x_52;
goto _start;
}
}
case 3:
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_28);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_dec(x_12);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_15, 4);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_16, 1);
x_59 = lean_ctor_get(x_16, 0);
lean_dec(x_59);
lean_ctor_set(x_15, 4, x_58);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 0, x_15);
x_8 = lean_box(0);
x_12 = x_54;
x_13 = x_16;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_16, 1);
lean_inc(x_61);
lean_dec(x_16);
lean_ctor_set(x_15, 4, x_61);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_15);
lean_ctor_set(x_62, 1, x_13);
x_8 = lean_box(0);
x_12 = x_54;
x_13 = x_62;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
x_66 = lean_ctor_get(x_15, 2);
x_67 = lean_ctor_get(x_15, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_68 = lean_ctor_get(x_16, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_69 = x_16;
} else {
 lean_dec_ref(x_16);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_13);
x_8 = lean_box(0);
x_12 = x_54;
x_13 = x_71;
goto _start;
}
}
default: 
{
uint8_t x_73; 
lean_dec(x_28);
lean_dec(x_15);
x_73 = !lean_is_exclusive(x_16);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_16, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_16, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_78 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_77);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 0, x_78);
x_8 = lean_box(0);
x_12 = x_76;
x_13 = x_16;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_16);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_dec(x_12);
x_81 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__2;
x_82 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__2(x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_13);
x_8 = lean_box(0);
x_12 = x_80;
x_13 = x_83;
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
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_mkFVar(x_7);
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
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkFVar(x_12);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__9(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
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
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__2(x_3, x_19, x_21, x_22);
lean_dec(x_19);
x_24 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__3(x_4, x_23, x_22);
x_25 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__4(x_1, x_20, x_22);
lean_inc(x_4);
x_26 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_2, x_5, x_6, x_7, x_8, x_9, lean_box(0), x_4, x_10, x_13, x_25, x_22);
x_27 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_2, x_11, x_5, x_6, x_7, x_8, x_9, lean_box(0), x_1, x_10, x_13, x_26, x_22);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_2, 0);
lean_dec(x_32);
x_33 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_4, x_12, x_22);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_ctor_set(x_2, 3, x_24);
lean_ctor_set(x_2, 2, x_27);
lean_ctor_set(x_2, 1, x_33);
lean_ctor_set(x_2, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_18);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
x_36 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__7(x_4, x_12, x_22);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_24);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_18);
return x_39;
}
}
}
static lean_object* _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processValue subst: ");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(x_20, x_23);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_3, 2, x_24);
lean_ctor_set(x_3, 1, x_26);
lean_ctor_set(x_3, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_16);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_3, 2);
x_29 = lean_ctor_get(x_3, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_30 = lean_box(0);
x_31 = l_List_filterAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__1(x_28, x_30);
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_16);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_5);
x_36 = lean_array_fget(x_1, x_2);
x_37 = lean_ctor_get(x_4, 2);
lean_inc(x_37);
x_62 = lean_st_ref_get(x_15, x_16);
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
x_38 = x_67;
x_39 = x_66;
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
lean_inc(x_10);
x_69 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_10, x_12, x_13, x_14, x_15, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_38 = x_72;
x_39 = x_71;
goto block_61;
}
block_61:
{
if (x_38 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
x_40 = lean_box(0);
x_41 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__1(x_36, x_3, x_7, x_37, x_8, x_2, x_4, x_9, x_11, x_38, x_1, x_6, x_40, x_12, x_13, x_14, x_15, x_39);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_8);
lean_dec(x_7);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = l_Std_AssocList_toList___rarg(x_37);
x_43 = lean_box(0);
lean_inc(x_42);
x_44 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__8(x_42, x_43);
x_45 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_44, x_43);
x_46 = l_Lean_MessageData_ofList(x_45);
lean_dec(x_45);
x_47 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__9(x_42, x_43);
x_52 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_51, x_43);
x_53 = l_Lean_MessageData_ofList(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_10, x_56, x_12, x_13, x_14, x_15, x_39);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__1(x_36, x_3, x_7, x_37, x_8, x_2, x_4, x_9, x_11, x_38, x_1, x_6, x_58, x_12, x_13, x_14, x_15, x_59);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_58);
lean_dec(x_1);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_8);
lean_dec(x_7);
return x_60;
}
}
}
}
}
static lean_object* _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processValue subgoal\n");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_9, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_9, x_20);
lean_dec(x_9);
x_22 = lean_array_fget(x_8, x_10);
x_48 = lean_st_ref_get(x_16, x_17);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 3);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*1);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = 0;
x_23 = x_53;
x_24 = x_52;
goto block_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
lean_inc(x_2);
x_55 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_13, x_14, x_15, x_16, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_23 = x_58;
x_24 = x_57;
goto block_47;
}
block_47:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_5);
x_26 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2(x_5, x_10, x_1, x_22, x_3, x_4, x_6, x_7, x_23, x_2, x_25, x_13, x_14, x_15, x_16, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_add(x_10, x_20);
lean_dec(x_10);
x_30 = lean_array_push(x_12, x_27);
x_9 = x_21;
x_10 = x_29;
x_11 = lean_box(0);
x_12 = x_30;
x_17 = x_28;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_2);
x_38 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_37, x_13, x_14, x_15, x_16, x_24);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_5);
x_41 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2(x_5, x_10, x_1, x_22, x_3, x_4, x_6, x_7, x_23, x_2, x_39, x_13, x_14, x_15, x_16, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_nat_add(x_10, x_20);
lean_dec(x_10);
x_45 = lean_array_push(x_12, x_42);
x_9 = x_21;
x_10 = x_44;
x_11 = lean_box(0);
x_12 = x_45;
x_17 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_17);
return x_59;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___closed__1;
x_3 = lean_unsigned_to_nat(456u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1___closed__1;
x_11 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_1);
x_14 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectValues(x_1);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_12);
x_16 = l_Lean_Expr_fvarId_x21(x_12);
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
x_18 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
lean_inc(x_16);
x_19 = l_Lean_Meta_caseValues(x_15, x_16, x_14, x_17, x_18, x_4, x_5, x_6, x_7, x_8);
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
lean_inc(x_20);
x_25 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10(x_1, x_2, x_12, x_13, x_14, x_16, x_20, x_20, x_22, x_24, lean_box(0), x_23, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_20);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_25 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_7, x_2, x_3, x_4, x_5, x_24);
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
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(x_1, x_7, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___closed__2;
x_13 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_7, x_12, x_2, x_3, x_4, x_5, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___lambda__1(x_1, x_7, x_14, x_2, x_3, x_4, x_5, x_15);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_9);
lean_dec(x_9);
x_15 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__5(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_14, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = lean_unbox(x_10);
lean_dec(x_10);
x_16 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__6(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_15, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__1___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = lean_unbox(x_10);
lean_dec(x_10);
x_21 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_9, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
return x_18;
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
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
lean_dec(x_6);
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
lean_inc(x_6);
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
lean_inc(x_6);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(536u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_dec(x_9);
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
lean_object* x_37; lean_object* x_38; 
lean_dec(x_18);
x_37 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_38 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(x_37, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_21 = x_39;
x_22 = x_40;
goto block_35;
}
else
{
uint8_t x_41; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
switch (lean_obj_tag(x_45)) {
case 1:
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
x_49 = lean_ctor_get(x_18, 2);
x_50 = lean_ctor_get(x_18, 3);
x_51 = lean_ctor_get(x_18, 4);
lean_dec(x_51);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_dec(x_36);
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
lean_inc(x_2);
lean_inc(x_9);
x_54 = l_Lean_Meta_FVarSubst_apply(x_9, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_55 = l_Lean_Meta_getArrayArgType(x_54, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_18, 4, x_52);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
x_58 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(x_18, x_53, x_56, x_8, x_11, x_12, x_13, x_14, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_21 = x_59;
x_22 = x_60;
goto block_35;
}
else
{
uint8_t x_61; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
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
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_18);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
x_71 = lean_ctor_get(x_18, 2);
x_72 = lean_ctor_get(x_18, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
x_73 = lean_ctor_get(x_36, 1);
lean_inc(x_73);
lean_dec(x_36);
x_74 = lean_ctor_get(x_45, 0);
lean_inc(x_74);
lean_dec(x_45);
lean_inc(x_2);
lean_inc(x_9);
x_75 = l_Lean_Meta_FVarSubst_apply(x_9, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_76 = l_Lean_Meta_getArrayArgType(x_75, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_71);
lean_ctor_set(x_79, 3, x_72);
lean_ctor_set(x_79, 4, x_73);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
x_80 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandVarIntoArrayLit(x_79, x_74, x_77, x_8, x_11, x_12, x_13, x_14, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_21 = x_81;
x_22 = x_82;
goto block_35;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_85 = x_80;
} else {
 lean_dec_ref(x_80);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_89 = x_76;
} else {
 lean_dec_ref(x_76);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
case 4:
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_18);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_18, 4);
lean_dec(x_92);
x_93 = lean_ctor_get(x_36, 1);
lean_inc(x_93);
lean_dec(x_36);
x_94 = lean_ctor_get(x_45, 1);
lean_inc(x_94);
lean_dec(x_45);
x_95 = l_List_appendTR___rarg(x_94, x_93);
lean_ctor_set(x_18, 4, x_95);
x_21 = x_18;
x_22 = x_15;
goto block_35;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_18, 0);
x_97 = lean_ctor_get(x_18, 1);
x_98 = lean_ctor_get(x_18, 2);
x_99 = lean_ctor_get(x_18, 3);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_18);
x_100 = lean_ctor_get(x_36, 1);
lean_inc(x_100);
lean_dec(x_36);
x_101 = lean_ctor_get(x_45, 1);
lean_inc(x_101);
lean_dec(x_45);
x_102 = l_List_appendTR___rarg(x_101, x_100);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set(x_103, 2, x_98);
lean_ctor_set(x_103, 3, x_99);
lean_ctor_set(x_103, 4, x_102);
x_21 = x_103;
x_22 = x_15;
goto block_35;
}
}
default: 
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_45);
lean_dec(x_36);
lean_dec(x_18);
x_104 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__2;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_105 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__1(x_104, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_21 = x_106;
x_22 = x_107;
goto block_35;
}
else
{
uint8_t x_108; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
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
lean_inc(x_38);
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
lean_inc(x_38);
x_51 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__7(x_1, x_6, x_9, x_21, lean_box(0), x_38, x_50, x_40);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_2);
x_52 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8(x_1, x_2, x_4, x_6, x_9, x_21, lean_box(0), x_35, x_38, x_51, x_12, x_13, x_14, x_15, x_16);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__8___closed__1;
x_3 = lean_unsigned_to_nat(512u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__1;
x_10 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_collectArraySizes(x_1);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_inc(x_11);
x_15 = l_Lean_Expr_fvarId_x21(x_11);
x_16 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___lambda__1___closed__3;
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_15);
x_18 = l_Lean_Meta_caseArraySizes(x_14, x_15, x_13, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_19);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit___spec__9(x_1, x_11, x_12, x_13, x_15, x_19, x_19, x_21, x_23, lean_box(0), x_22, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_25 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_7, x_2, x_3, x_4, x_5, x_24);
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
x_13 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_7, x_12, x_2, x_3, x_4, x_5, x_9);
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
x_19 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_1, x_3, x_4, x_5, x_6, x_18);
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
x_32 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_30, x_3, x_4, x_5, x_6, x_31);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
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
x_29 = lean_ctor_get(x_6, 8);
x_30 = l_Lean_replaceRef(x_20, x_24);
lean_dec(x_20);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_25);
lean_ctor_set(x_31, 5, x_26);
lean_ctor_set(x_31, 6, x_27);
lean_ctor_set(x_31, 7, x_28);
lean_ctor_set(x_31, 8, x_29);
x_32 = 0;
lean_inc(x_7);
lean_inc(x_31);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_32, x_19, x_4, x_5, x_31, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_7);
lean_inc(x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_36 = lean_infer_type(x_1, x_4, x_5, x_31, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_7);
lean_inc(x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_34);
x_39 = lean_infer_type(x_34, x_4, x_5, x_31, x_7, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_7);
lean_inc(x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_40);
lean_inc(x_37);
x_42 = l_Lean_Meta_isExprDefEq(x_37, x_40, x_4, x_5, x_31, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_1);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_31);
lean_inc(x_5);
lean_inc(x_4);
x_46 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_40, x_37, x_4, x_5, x_31, x_7, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_indentExpr(x_34);
x_50 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__3;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwCasesException___rarg___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
x_55 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_56, x_4, x_5, x_31, x_7, x_48);
lean_dec(x_7);
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_dec(x_42);
x_63 = l_List_forIn_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1___closed__1;
x_12 = x_63;
x_13 = x_62;
goto block_16;
}
}
else
{
uint8_t x_64; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_42);
if (x_64 == 0)
{
return x_42;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_42, 0);
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_42);
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
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_39);
if (x_68 == 0)
{
return x_39;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_39, 0);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_39);
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
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_36);
if (x_72 == 0)
{
return x_36;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_36, 0);
x_74 = lean_ctor_get(x_36, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_36);
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
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_33);
if (x_76 == 0)
{
return x_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_33, 0);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_33);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
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
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_panic_fn(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___spec__1___rarg), 2, 0);
return x_2;
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__1;
x_3 = lean_unsigned_to_nat(585u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg___closed__2;
x_5 = l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___spec__1___rarg(x_1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(x_1, x_8, x_12);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_13, 1, x_2);
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
lean_ctor_set(x_2, 1, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_free_object(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_3, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_3, x_24);
x_26 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront_loop___rarg(x_1, x_21, x_25);
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
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
return x_32;
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 4);
x_10 = l_Lean_Meta_Match_instInhabitedPattern;
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(x_10, x_9, x_1);
lean_ctor_set(x_6, 4, x_11);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 2);
x_17 = lean_ctor_get(x_6, 3);
x_18 = lean_ctor_get(x_6, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_19 = l_Lean_Meta_Match_instInhabitedPattern;
x_20 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(x_19, x_18, x_1);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_21);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 4);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Meta_Match_instInhabitedPattern;
x_32 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(x_31, x_29, x_1);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 5, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_2 = x_24;
x_3 = x_34;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = l_Lean_instInhabitedExpr;
x_17 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(x_16, x_6, x_2);
x_18 = lean_box(0);
x_19 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(x_2, x_7, x_18);
lean_ctor_set(x_1, 2, x_19);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_20 = l_Lean_instInhabitedExpr;
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_List_moveToFront___rarg(x_20, x_6, x_2);
x_22 = lean_box(0);
x_23 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(x_2, x_7, x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_8);
return x_24;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_moveToFront___spec__1(x_1, x_2, x_3);
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
x_1 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1;
x_2 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1;
x_3 = lean_unsigned_to_nat(652u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3;
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
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2;
x_12 = l_panic___at_Lean_Meta_ACLt_lt_lexSameCtor___spec__1(x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = l_Lean_Expr_isFVar(x_13);
if (x_17 == 0)
{
lean_dec(x_13);
x_1 = x_14;
x_2 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lean_Expr_fvarId_x21(x_13);
lean_inc(x_3);
x_20 = l_Lean_Meta_dependsOn(x_3, x_19, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_1 = x_14;
x_2 = x_16;
x_8 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_List_lengthTRAux___rarg(x_8, x_9);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_14 = l_List_get___rarg(x_8, x_2);
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
lean_dec(x_1);
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
else
{
uint8_t x_35; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
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
x_18 = lean_usize_add(x_2, x_17);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nat value to constructor");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variable");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non variable");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("as-pattern");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 8);
lean_inc(x_16);
x_17 = lean_nat_dec_eq(x_9, x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_5, 8);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 7);
lean_dec(x_20);
x_21 = lean_ctor_get(x_5, 6);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 5);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 4);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 0);
lean_dec(x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_30 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_32 = l_Lean_Meta_Match_isCurrVarInductive(x_1, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_130; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_130 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_1);
if (x_130 == 0)
{
uint8_t x_131; 
lean_inc(x_1);
x_131 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_1);
if (x_131 == 0)
{
uint8_t x_132; 
lean_inc(x_1);
x_132 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_1);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_1);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_33);
x_134 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__3;
x_135 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_134, x_2, x_3, x_4, x_5, x_6, x_34);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_137 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(x_1, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_unsigned_to_nat(0u);
x_141 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_138, x_140, x_2, x_3, x_4, x_5, x_6, x_139);
return x_141;
}
else
{
uint8_t x_142; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_137);
if (x_142 == 0)
{
return x_137;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_137, 0);
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_137);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
x_146 = lean_unbox(x_33);
lean_dec(x_33);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_35 = x_147;
goto block_129;
}
else
{
uint8_t x_148; 
lean_inc(x_1);
x_148 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_1);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_35 = x_149;
goto block_129;
}
else
{
lean_object* x_150; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_150 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_150, 0);
x_153 = lean_ctor_get(x_150, 1);
x_154 = lean_array_get_size(x_152);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_nat_dec_lt(x_155, x_154);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_box(0);
lean_ctor_set(x_150, 0, x_157);
return x_150;
}
else
{
uint8_t x_158; 
x_158 = lean_nat_dec_le(x_154, x_154);
if (x_158 == 0)
{
lean_object* x_159; 
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = lean_box(0);
lean_ctor_set(x_150, 0, x_159);
return x_150;
}
else
{
size_t x_160; size_t x_161; lean_object* x_162; lean_object* x_163; 
lean_free_object(x_150);
x_160 = 0;
x_161 = lean_usize_of_nat(x_154);
lean_dec(x_154);
x_162 = lean_box(0);
x_163 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_152, x_160, x_161, x_162, x_2, x_3, x_4, x_5, x_6, x_153);
lean_dec(x_152);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_150, 0);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_150);
x_166 = lean_array_get_size(x_164);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_lt(x_167, x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_165);
return x_170;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_166, x_166);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_165);
return x_173;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; lean_object* x_177; 
x_174 = 0;
x_175 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_176 = lean_box(0);
x_177 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_164, x_174, x_175, x_176, x_2, x_3, x_4, x_5, x_6, x_165);
lean_dec(x_164);
return x_177;
}
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = !lean_is_exclusive(x_150);
if (x_178 == 0)
{
return x_150;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_150, 0);
x_180 = lean_ctor_get(x_150, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_150);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_33);
x_182 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1;
x_183 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_182, x_2, x_3, x_4, x_5, x_6, x_34);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_1);
x_186 = lean_unsigned_to_nat(0u);
x_187 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_185, x_186, x_2, x_3, x_4, x_5, x_6, x_184);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_33);
x_188 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__4;
x_189 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_188, x_2, x_3, x_4, x_5, x_6, x_34);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_191 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(x_1, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_unsigned_to_nat(0u);
x_195 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_192, x_194, x_2, x_3, x_4, x_5, x_6, x_193);
return x_195;
}
else
{
uint8_t x_196; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_196 = !lean_is_exclusive(x_191);
if (x_196 == 0)
{
return x_191;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_191, 0);
x_198 = lean_ctor_get(x_191, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_191);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
else
{
lean_object* x_200; 
lean_dec(x_33);
x_200 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(x_1, x_2, x_3, x_4, x_5, x_6, x_34);
return x_200;
}
block_129:
{
uint8_t x_36; 
lean_dec(x_35);
lean_inc(x_1);
x_36 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_1);
if (x_36 == 0)
{
uint8_t x_37; 
lean_inc(x_1);
x_37 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_1);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc(x_1);
x_38 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_1);
if (x_38 == 0)
{
uint8_t x_39; 
lean_inc(x_1);
x_39 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_1);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_40 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(x_1, x_3, x_4, x_5, x_6, x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1;
x_48 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_47, x_2, x_3, x_4, x_5, x_6, x_34);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_1);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_50, x_51, x_2, x_3, x_4, x_5, x_6, x_49);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_53 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_array_get_size(x_55);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_lt(x_58, x_57);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
lean_ctor_set(x_53, 0, x_60);
return x_53;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_57, x_57);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(0);
lean_ctor_set(x_53, 0, x_62);
return x_53;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_53);
x_63 = 0;
x_64 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_65 = lean_box(0);
x_66 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_55, x_63, x_64, x_65, x_2, x_3, x_4, x_5, x_6, x_56);
lean_dec(x_55);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_69 = lean_array_get_size(x_67);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_lt(x_70, x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_69, x_69);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
else
{
size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_77 = 0;
x_78 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_79 = lean_box(0);
x_80 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_67, x_77, x_78, x_79, x_2, x_3, x_4, x_5, x_6, x_68);
lean_dec(x_67);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_53);
if (x_81 == 0)
{
return x_53;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_53, 0);
x_83 = lean_ctor_get(x_53, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_53);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_85 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_array_get_size(x_87);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_nat_dec_lt(x_90, x_89);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(0);
lean_ctor_set(x_85, 0, x_92);
return x_85;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_89, x_89);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_box(0);
lean_ctor_set(x_85, 0, x_94);
return x_85;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
lean_free_object(x_85);
x_95 = 0;
x_96 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_97 = lean_box(0);
x_98 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_87, x_95, x_96, x_97, x_2, x_3, x_4, x_5, x_6, x_88);
lean_dec(x_87);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_85, 0);
x_100 = lean_ctor_get(x_85, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_85);
x_101 = lean_array_get_size(x_99);
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_nat_dec_lt(x_102, x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
else
{
uint8_t x_106; 
x_106 = lean_nat_dec_le(x_101, x_101);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
return x_108;
}
else
{
size_t x_109; size_t x_110; lean_object* x_111; lean_object* x_112; 
x_109 = 0;
x_110 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_111 = lean_box(0);
x_112 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_99, x_109, x_110, x_111, x_2, x_3, x_4, x_5, x_6, x_100);
lean_dec(x_99);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_85);
if (x_113 == 0)
{
return x_85;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_85, 0);
x_115 = lean_ctor_get(x_85, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_85);
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
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2;
x_118 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_117, x_2, x_3, x_4, x_5, x_6, x_34);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_1, x_3, x_4, x_5, x_6, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_unsigned_to_nat(0u);
x_124 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_121, x_123, x_2, x_3, x_4, x_5, x_6, x_122);
return x_124;
}
else
{
uint8_t x_125; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_120);
if (x_125 == 0)
{
return x_120;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_120, 0);
x_127 = lean_ctor_get(x_120, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_120);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_32);
if (x_201 == 0)
{
return x_32;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_32, 0);
x_203 = lean_ctor_get(x_32, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_32);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_30);
if (x_205 == 0)
{
return x_30;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_30, 0);
x_207 = lean_ctor_get(x_30, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_30);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_5);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_9, x_209);
lean_dec(x_9);
x_211 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_211, 0, x_8);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_10);
lean_ctor_set(x_211, 3, x_11);
lean_ctor_set(x_211, 4, x_12);
lean_ctor_set(x_211, 5, x_13);
lean_ctor_set(x_211, 6, x_14);
lean_ctor_set(x_211, 7, x_15);
lean_ctor_set(x_211, 8, x_16);
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_212 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceState(x_1, x_3, x_4, x_211, x_6, x_7);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_214 = l_Lean_Meta_Match_isCurrVarInductive(x_1, x_3, x_4, x_211, x_6, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_288; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_288 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isDone(x_1);
if (x_288 == 0)
{
uint8_t x_289; 
lean_inc(x_1);
x_289 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasAsPattern(x_1);
if (x_289 == 0)
{
uint8_t x_290; 
lean_inc(x_1);
x_290 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNatValueTransition(x_1);
if (x_290 == 0)
{
uint8_t x_291; 
x_291 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isNextVar(x_1);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_215);
x_292 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__3;
x_293 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_292, x_2, x_3, x_4, x_211, x_6, x_216);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
x_295 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processNonVariable(x_1, x_3, x_4, x_211, x_6, x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_unsigned_to_nat(0u);
x_299 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_296, x_298, x_2, x_3, x_4, x_211, x_6, x_297);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_300 = lean_ctor_get(x_295, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_295, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_302 = x_295;
} else {
 lean_dec_ref(x_295);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
else
{
uint8_t x_304; 
x_304 = lean_unbox(x_215);
lean_dec(x_215);
if (x_304 == 0)
{
lean_object* x_305; 
x_305 = lean_box(0);
x_217 = x_305;
goto block_287;
}
else
{
uint8_t x_306; 
lean_inc(x_1);
x_306 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isConstructorTransition(x_1);
if (x_306 == 0)
{
lean_object* x_307; 
x_307 = lean_box(0);
x_217 = x_307;
goto block_287;
}
else
{
lean_object* x_308; 
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
x_308 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor(x_1, x_3, x_4, x_211, x_6, x_216);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
x_312 = lean_array_get_size(x_309);
x_313 = lean_unsigned_to_nat(0u);
x_314 = lean_nat_dec_lt(x_313, x_312);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_312);
lean_dec(x_309);
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_315 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_311;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_310);
return x_316;
}
else
{
uint8_t x_317; 
x_317 = lean_nat_dec_le(x_312, x_312);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_312);
lean_dec(x_309);
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_318 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_311;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_310);
return x_319;
}
else
{
size_t x_320; size_t x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_311);
x_320 = 0;
x_321 = lean_usize_of_nat(x_312);
lean_dec(x_312);
x_322 = lean_box(0);
x_323 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_309, x_320, x_321, x_322, x_2, x_3, x_4, x_211, x_6, x_310);
lean_dec(x_309);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_324 = lean_ctor_get(x_308, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_308, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_326 = x_308;
} else {
 lean_dec_ref(x_308);
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
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_215);
x_328 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1;
x_329 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_328, x_2, x_3, x_4, x_211, x_6, x_216);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_331 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_1);
x_332 = lean_unsigned_to_nat(0u);
x_333 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_331, x_332, x_2, x_3, x_4, x_211, x_6, x_330);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_215);
x_334 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__4;
x_335 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_334, x_2, x_3, x_4, x_211, x_6, x_216);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
lean_dec(x_335);
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
x_337 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern(x_1, x_3, x_4, x_211, x_6, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_unsigned_to_nat(0u);
x_341 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_338, x_340, x_2, x_3, x_4, x_211, x_6, x_339);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_342 = lean_ctor_get(x_337, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_337, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_344 = x_337;
} else {
 lean_dec_ref(x_337);
 x_344 = lean_box(0);
}
if (lean_is_scalar(x_344)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_344;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
}
}
else
{
lean_object* x_346; 
lean_dec(x_215);
x_346 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processLeaf(x_1, x_2, x_3, x_4, x_211, x_6, x_216);
return x_346;
}
block_287:
{
uint8_t x_218; 
lean_dec(x_217);
lean_inc(x_1);
x_218 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isVariableTransition(x_1);
if (x_218 == 0)
{
uint8_t x_219; 
lean_inc(x_1);
x_219 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isValueTransition(x_1);
if (x_219 == 0)
{
uint8_t x_220; 
lean_inc(x_1);
x_220 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_isArrayLitTransition(x_1);
if (x_220 == 0)
{
uint8_t x_221; 
lean_inc(x_1);
x_221 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_hasNatValPattern(x_1);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_222 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes(x_1, x_3, x_4, x_211, x_6, x_216);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_throwNonSupported(x_1, x_3, x_4, x_211, x_6, x_223);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_227 = x_222;
} else {
 lean_dec_ref(x_222);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1;
x_230 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_229, x_2, x_3, x_4, x_211, x_6, x_216);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_expandNatValuePattern(x_1);
x_233 = lean_unsigned_to_nat(0u);
x_234 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_232, x_233, x_2, x_3, x_4, x_211, x_6, x_231);
return x_234;
}
}
else
{
lean_object* x_235; 
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
x_235 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processArrayLit(x_1, x_3, x_4, x_211, x_6, x_216);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_array_get_size(x_236);
x_240 = lean_unsigned_to_nat(0u);
x_241 = lean_nat_dec_lt(x_240, x_239);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_238;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_237);
return x_243;
}
else
{
uint8_t x_244; 
x_244 = lean_nat_dec_le(x_239, x_239);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_239);
lean_dec(x_236);
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_238;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_237);
return x_246;
}
else
{
size_t x_247; size_t x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_238);
x_247 = 0;
x_248 = lean_usize_of_nat(x_239);
lean_dec(x_239);
x_249 = lean_box(0);
x_250 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_236, x_247, x_248, x_249, x_2, x_3, x_4, x_211, x_6, x_237);
lean_dec(x_236);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_251 = lean_ctor_get(x_235, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_235, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_253 = x_235;
} else {
 lean_dec_ref(x_235);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
}
else
{
lean_object* x_255; 
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
x_255 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue(x_1, x_3, x_4, x_211, x_6, x_216);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
x_259 = lean_array_get_size(x_256);
x_260 = lean_unsigned_to_nat(0u);
x_261 = lean_nat_dec_lt(x_260, x_259);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_259);
lean_dec(x_256);
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_262 = lean_box(0);
if (lean_is_scalar(x_258)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_258;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_257);
return x_263;
}
else
{
uint8_t x_264; 
x_264 = lean_nat_dec_le(x_259, x_259);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_259);
lean_dec(x_256);
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_265 = lean_box(0);
if (lean_is_scalar(x_258)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_258;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_257);
return x_266;
}
else
{
size_t x_267; size_t x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_258);
x_267 = 0;
x_268 = lean_usize_of_nat(x_259);
lean_dec(x_259);
x_269 = lean_box(0);
x_270 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__1(x_256, x_267, x_268, x_269, x_2, x_3, x_4, x_211, x_6, x_257);
lean_dec(x_256);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_271 = lean_ctor_get(x_255, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_255, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_273 = x_255;
} else {
 lean_dec_ref(x_255);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2;
x_276 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_traceStep(x_275, x_2, x_3, x_4, x_211, x_6, x_216);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
lean_inc(x_6);
lean_inc(x_211);
lean_inc(x_4);
lean_inc(x_3);
x_278 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable(x_1, x_3, x_4, x_211, x_6, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_unsigned_to_nat(0u);
x_282 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_search(x_279, x_281, x_2, x_3, x_4, x_211, x_6, x_280);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_283 = lean_ctor_get(x_278, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_285 = x_278;
} else {
 lean_dec_ref(x_278);
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
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_347 = lean_ctor_get(x_214, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_214, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_349 = x_214;
} else {
 lean_dec_ref(x_214);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_351 = lean_ctor_get(x_212, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_212, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_353 = x_212;
} else {
 lean_dec_ref(x_212);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
}
else
{
lean_object* x_355; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_355 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_355;
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
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_findNext), 7, 2);
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bootstrap");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("genMatcherCode");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__2;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("disable code generation for auxiliary matcher function");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__1;
x_3 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__4;
x_3 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__6;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_54____spec__1(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____lambda__1(uint8_t x_1, uint8_t x_2) {
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
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__2;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instHashableBool___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__4;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__8;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__9;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____lambda__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_expr_eqv(x_10, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_unbox(x_11);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_unbox(x_13);
lean_dec(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_4, x_22);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_23;
goto _start;
}
}
else
{
uint8_t x_25; 
x_25 = lean_unbox(x_13);
lean_dec(x_13);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_expr_eqv(x_13, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_12);
x_18 = lean_box(0);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_unbox(x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_unbox(x_16);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_12);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = lean_box(0);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = lean_unbox(x_16);
lean_dec(x_16);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_12);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_12);
return x_25;
}
}
}
}
case 1:
{
lean_object* x_26; size_t x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_usize_shift_right(x_2, x_5);
x_1 = x_26;
x_2 = x_27;
goto _start;
}
default: 
{
lean_object* x_29; 
x_29 = lean_box(0);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__3(x_30, x_31, lean_box(0), x_32, x_3);
lean_dec(x_31);
lean_dec(x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Expr_hash(x_4);
lean_dec(x_4);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
if (x_7 == 0)
{
uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; 
x_8 = 13;
x_9 = lean_uint64_mix_hash(x_6, x_8);
x_10 = lean_uint64_to_usize(x_9);
x_11 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2(x_3, x_10, x_2);
lean_dec(x_2);
return x_11;
}
else
{
uint64_t x_12; uint64_t x_13; size_t x_14; lean_object* x_15; 
x_12 = 11;
x_13 = lean_uint64_mix_hash(x_6, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2(x_3, x_14, x_2);
lean_dec(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint8_t x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
x_19 = l_Lean_Expr_hash(x_17);
lean_dec(x_17);
x_20 = lean_unbox(x_18);
lean_dec(x_18);
if (x_20 == 0)
{
uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = 13;
x_22 = lean_uint64_mix_hash(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_shift_right(x_23, x_14);
x_25 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_6, x_24, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_25;
goto _start;
}
else
{
uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_27 = 11;
x_28 = lean_uint64_mix_hash(x_19, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_shift_right(x_29, x_14);
x_31 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_6, x_30, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_array_fget(x_5, x_2);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_expr_eqv(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
x_2 = x_29;
goto _start;
}
else
{
uint8_t x_31; 
x_31 = lean_unbox(x_24);
lean_dec(x_24);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = lean_unbox(x_26);
lean_dec(x_26);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = lean_box(0);
x_17 = x_33;
goto block_21;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_2 = x_35;
goto _start;
}
}
else
{
uint8_t x_37; 
x_37 = lean_unbox(x_26);
lean_dec(x_26);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_6);
lean_dec(x_5);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
lean_dec(x_2);
x_2 = x_39;
goto _start;
}
else
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_box(0);
x_17 = x_41;
goto block_21;
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = lean_array_fset(x_5, x_2, x_3);
x_19 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = lean_expr_eqv(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_15);
x_26 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_array_fset(x_17, x_12, x_27);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
uint8_t x_29; 
x_29 = lean_unbox(x_22);
lean_dec(x_22);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = lean_unbox(x_24);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_31 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_15);
x_32 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_array_fset(x_17, x_12, x_33);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
}
else
{
uint8_t x_35; 
x_35 = lean_unbox(x_24);
lean_dec(x_24);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_15);
x_36 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_array_fset(x_17, x_12, x_37);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_38);
return x_1;
}
else
{
lean_object* x_39; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
x_46 = lean_expr_eqv(x_42, x_44);
lean_dec(x_44);
lean_dec(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_40, x_41, x_4, x_5);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
else
{
uint8_t x_50; 
x_50 = lean_unbox(x_43);
lean_dec(x_43);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = lean_unbox(x_45);
lean_dec(x_45);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_41);
lean_dec(x_40);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_5);
x_53 = lean_array_fset(x_17, x_12, x_52);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_40, x_41, x_4, x_5);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_array_fset(x_17, x_12, x_55);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_56);
return x_1;
}
}
else
{
uint8_t x_57; 
x_57 = lean_unbox(x_45);
lean_dec(x_45);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_40, x_41, x_4, x_5);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_array_fset(x_17, x_12, x_59);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_40);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_5);
x_62 = lean_array_fset(x_17, x_12, x_61);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_62);
return x_1;
}
}
}
}
}
case 1:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_15);
if (x_63 == 0)
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_usize_shift_right(x_2, x_9);
x_66 = lean_usize_add(x_3, x_8);
x_67 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_64, x_65, x_66, x_4, x_5);
lean_ctor_set(x_15, 0, x_67);
x_68 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_68);
return x_1;
}
else
{
lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_15, 0);
lean_inc(x_69);
lean_dec(x_15);
x_70 = lean_usize_shift_right(x_2, x_9);
x_71 = lean_usize_add(x_3, x_8);
x_72 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_69, x_70, x_71, x_4, x_5);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_array_fset(x_17, x_12, x_73);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_74);
return x_1;
}
}
default: 
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_4);
lean_ctor_set(x_75, 1, x_5);
x_76 = lean_array_fset(x_17, x_12, x_75);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_76);
return x_1;
}
}
}
}
else
{
lean_object* x_77; size_t x_78; size_t x_79; size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
lean_dec(x_1);
x_78 = 1;
x_79 = 5;
x_80 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__2;
x_81 = lean_usize_land(x_2, x_80);
x_82 = lean_usize_to_nat(x_81);
x_83 = lean_array_get_size(x_77);
x_84 = lean_nat_dec_lt(x_82, x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_5);
lean_dec(x_4);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_array_fget(x_77, x_82);
x_87 = lean_box(0);
x_88 = lean_array_fset(x_77, x_82, x_87);
switch (lean_obj_tag(x_86)) {
case 0:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_91 = x_86;
} else {
 lean_dec_ref(x_86);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
x_96 = lean_expr_eqv(x_92, x_94);
lean_dec(x_94);
lean_dec(x_92);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_91);
x_97 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_89, x_90, x_4, x_5);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_array_fset(x_88, x_82, x_98);
lean_dec(x_82);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
else
{
uint8_t x_101; 
x_101 = lean_unbox(x_93);
lean_dec(x_93);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_unbox(x_95);
lean_dec(x_95);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_89);
if (lean_is_scalar(x_91)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_91;
}
lean_ctor_set(x_103, 0, x_4);
lean_ctor_set(x_103, 1, x_5);
x_104 = lean_array_fset(x_88, x_82, x_103);
lean_dec(x_82);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_91);
x_106 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_89, x_90, x_4, x_5);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_array_fset(x_88, x_82, x_107);
lean_dec(x_82);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
else
{
uint8_t x_110; 
x_110 = lean_unbox(x_95);
lean_dec(x_95);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_91);
x_111 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_89, x_90, x_4, x_5);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_array_fset(x_88, x_82, x_112);
lean_dec(x_82);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_90);
lean_dec(x_89);
if (lean_is_scalar(x_91)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_91;
}
lean_ctor_set(x_115, 0, x_4);
lean_ctor_set(x_115, 1, x_5);
x_116 = lean_array_fset(x_88, x_82, x_115);
lean_dec(x_82);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
case 1:
{
lean_object* x_118; lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_86, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_119 = x_86;
} else {
 lean_dec_ref(x_86);
 x_119 = lean_box(0);
}
x_120 = lean_usize_shift_right(x_2, x_79);
x_121 = lean_usize_add(x_3, x_78);
x_122 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_118, x_120, x_121, x_4, x_5);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_array_fset(x_88, x_82, x_123);
lean_dec(x_82);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
default: 
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_4);
lean_ctor_set(x_126, 1, x_5);
x_127 = lean_array_fset(x_88, x_82, x_126);
lean_dec(x_82);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_1);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; size_t x_132; uint8_t x_133; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__7(x_1, x_130, x_4, x_5);
x_132 = 7;
x_133 = lean_usize_dec_le(x_132, x_3);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_131);
x_135 = lean_unsigned_to_nat(4u);
x_136 = lean_nat_dec_lt(x_134, x_135);
lean_dec(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_131, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 1);
lean_inc(x_138);
lean_dec(x_131);
x_139 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___closed__1;
x_140 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__6(x_3, x_137, x_138, lean_box(0), x_130, x_139);
lean_dec(x_138);
lean_dec(x_137);
return x_140;
}
else
{
return x_131;
}
}
else
{
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; uint8_t x_147; 
x_141 = lean_ctor_get(x_1, 0);
x_142 = lean_ctor_get(x_1, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_1);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__7(x_143, x_144, x_4, x_5);
x_146 = 7;
x_147 = lean_usize_dec_le(x_146, x_3);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_145);
x_149 = lean_unsigned_to_nat(4u);
x_150 = lean_nat_dec_lt(x_148, x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_dec(x_145);
x_153 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___closed__1;
x_154 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__6(x_3, x_151, x_152, lean_box(0), x_144, x_153);
lean_dec(x_152);
lean_dec(x_151);
return x_154;
}
else
{
return x_145;
}
}
else
{
return x_145;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = 1;
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = l_Lean_Expr_hash(x_10);
lean_dec(x_10);
x_13 = lean_unbox(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
uint64_t x_14; uint64_t x_15; size_t x_16; lean_object* x_17; 
x_14 = 13;
x_15 = lean_uint64_mix_hash(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_5, x_16, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
else
{
uint64_t x_18; uint64_t x_19; size_t x_20; lean_object* x_21; 
x_18 = 11;
x_19 = lean_uint64_mix_hash(x_12, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_5, x_20, x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = 1;
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_23, x_25);
lean_dec(x_23);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = l_Lean_Expr_hash(x_27);
lean_dec(x_27);
x_30 = lean_unbox(x_28);
lean_dec(x_28);
if (x_30 == 0)
{
uint64_t x_31; uint64_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = 13;
x_32 = lean_uint64_mix_hash(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_22, x_33, x_24, x_2, x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
else
{
uint64_t x_36; uint64_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = 11;
x_37 = lean_uint64_mix_hash(x_29, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_22, x_38, x_24, x_2, x_3);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_26);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_insert___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__4(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_matcherExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_1);
x_11 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1), 3, 2);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_3);
x_19 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1;
x_20 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_19, x_17, x_18);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_st_ref_set(x_9, x_14, x_15);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_3);
x_23 = l_Lean_Meta_Match_addMatcherInfo(x_3, x_5, x_6, x_7, x_8, x_9, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Lean_Meta_setInlineAttribute(x_3, x_25, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_26) == 0)
{
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(x_1, x_6, x_7, x_8, x_9, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
x_41 = lean_ctor_get(x_14, 2);
x_42 = lean_ctor_get(x_14, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
lean_inc(x_3);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__1), 3, 2);
lean_closure_set(x_43, 0, x_2);
lean_closure_set(x_43, 1, x_3);
x_44 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1;
x_45 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_44, x_39, x_43);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
x_47 = lean_st_ref_set(x_9, x_46, x_15);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_3);
x_49 = l_Lean_Meta_Match_addMatcherInfo(x_3, x_5, x_6, x_7, x_8, x_9, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_52 = l_Lean_Meta_setInlineAttribute(x_3, x_51, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_52) == 0)
{
if (x_4 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = l_Lean_compileDecl___at_Lean_Meta_mkAuxDefinition___spec__3(x_1, x_6, x_7, x_8, x_9, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_61 = x_52;
} else {
 lean_dec_ref(x_52);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_11);
if (x_63 == 0)
{
return x_11;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_11, 0);
x_65 = lean_ctor_get(x_11, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_11);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_box(x_4);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___boxed), 10, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_ctor_get(x_5, 3);
lean_inc(x_14);
x_15 = lean_array_to_list(lean_box(0), x_14);
x_16 = l_Lean_mkConst(x_3, x_15);
x_17 = lean_ctor_get(x_5, 4);
lean_inc(x_17);
lean_dec(x_5);
x_18 = l_Lean_mkAppN(x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Match_bootstrap_genMatcherCode;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__3;
x_2 = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__5;
x_3 = l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__1;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__2;
x_24 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1;
x_25 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_23, x_24, x_22);
x_26 = lean_ctor_get(x_16, 2);
lean_inc(x_26);
x_27 = lean_box(x_13);
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_28);
x_29 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(x_25, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
lean_free_object(x_18);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_array_to_list(lean_box(0), x_30);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_32);
lean_inc(x_3);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_inc(x_32);
lean_inc(x_22);
x_34 = l_Lean_Environment_hasUnsafe(x_22, x_32);
if (x_34 == 0)
{
uint8_t x_71; 
lean_inc(x_26);
x_71 = l_Lean_Environment_hasUnsafe(x_22, x_26);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = 1;
x_35 = x_72;
goto block_70;
}
else
{
uint8_t x_73; 
x_73 = 0;
x_35 = x_73;
goto block_70;
}
}
else
{
uint8_t x_74; 
lean_dec(x_22);
x_74 = 0;
x_35 = x_74;
goto block_70;
}
block_70:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_36 = lean_box(1);
lean_inc(x_26);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_60 = lean_st_ref_get(x_9, x_21);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_39 = x_14;
x_40 = x_64;
goto block_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
lean_inc(x_4);
x_66 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_4, x_6, x_7, x_8, x_9, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_39 = x_69;
x_40 = x_68;
goto block_59;
}
block_59:
{
if (x_39 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_4);
x_41 = lean_box(0);
x_42 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_38, x_28, x_3, x_13, x_16, x_41, x_6, x_7, x_8, x_9, x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_3);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_3);
x_44 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_32);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_26);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
x_55 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_54, x_6, x_7, x_8, x_9, x_40);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_38, x_28, x_3, x_13, x_16, x_56, x_6, x_7, x_8, x_9, x_57);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_56);
return x_58;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_29, 0);
lean_inc(x_75);
lean_dec(x_29);
x_76 = lean_ctor_get(x_16, 3);
lean_inc(x_76);
x_77 = lean_array_to_list(lean_box(0), x_76);
x_78 = l_Lean_mkConst(x_75, x_77);
x_79 = lean_ctor_get(x_16, 4);
lean_inc(x_79);
lean_dec(x_16);
x_80 = l_Lean_mkAppN(x_78, x_79);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_18, 0, x_82);
return x_18;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_18, 0);
x_84 = lean_ctor_get(x_18, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_18);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__2;
x_87 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1;
x_88 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_86, x_87, x_85);
x_89 = lean_ctor_get(x_16, 2);
lean_inc(x_89);
x_90 = lean_box(x_13);
lean_inc(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_91);
x_92 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__1(x_88, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_16, 0);
lean_inc(x_93);
x_94 = lean_array_to_list(lean_box(0), x_93);
x_95 = lean_ctor_get(x_16, 1);
lean_inc(x_95);
lean_inc(x_95);
lean_inc(x_3);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_3);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_95);
lean_inc(x_95);
lean_inc(x_85);
x_97 = l_Lean_Environment_hasUnsafe(x_85, x_95);
if (x_97 == 0)
{
uint8_t x_134; 
lean_inc(x_89);
x_134 = l_Lean_Environment_hasUnsafe(x_85, x_89);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = 1;
x_98 = x_135;
goto block_133;
}
else
{
uint8_t x_136; 
x_136 = 0;
x_98 = x_136;
goto block_133;
}
}
else
{
uint8_t x_137; 
lean_dec(x_85);
x_137 = 0;
x_98 = x_137;
goto block_133;
}
block_133:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_99 = lean_box(1);
lean_inc(x_89);
x_100 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_89);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*3, x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_123 = lean_st_ref_get(x_9, x_84);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 3);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
lean_dec(x_123);
x_102 = x_14;
x_103 = x_127;
goto block_122;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_dec(x_123);
lean_inc(x_4);
x_129 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_4, x_6, x_7, x_8, x_9, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_unbox(x_130);
lean_dec(x_130);
x_102 = x_132;
x_103 = x_131;
goto block_122;
}
block_122:
{
if (x_102 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_95);
lean_dec(x_89);
lean_dec(x_4);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_101, x_91, x_3, x_13, x_16, x_104, x_6, x_7, x_8, x_9, x_103);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_inc(x_3);
x_106 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_106, 0, x_3);
x_107 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__12;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_111, 0, x_95);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Meta_Match_Unify_assign___closed__7;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_89);
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_107);
x_118 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_117, x_6, x_7, x_8, x_9, x_103);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_101, x_91, x_3, x_13, x_16, x_119, x_6, x_7, x_8, x_9, x_120);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_119);
return x_121;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_85);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_92, 0);
lean_inc(x_138);
lean_dec(x_92);
x_139 = lean_ctor_get(x_16, 3);
lean_inc(x_139);
x_140 = lean_array_to_list(lean_box(0), x_139);
x_141 = l_Lean_mkConst(x_138, x_140);
x_142 = lean_ctor_get(x_16, 4);
lean_inc(x_142);
lean_dec(x_16);
x_143 = l_Lean_mkAppN(x_141, x_142);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_84);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_15);
if (x_147 == 0)
{
return x_15;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_15, 0);
x_149 = lean_ctor_get(x_15, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_15);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
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
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_9, x_4, x_5, x_6, x_7, x_37);
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
x_26 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_9, x_25, x_4, x_5, x_6, x_7, x_11);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__3(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
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
x_8 = lean_ctor_get(x_5, 0);
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
LEAN_EXPORT uint8_t l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_List_elem___at_Lean_Occurrences_contains___spec__1(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_nat_add(x_8, x_7);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Std_HashSetImp_contains___at_Lean_Meta_Match_mkMatcher___spec__3(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_4);
x_3 = x_8;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_3 = x_8;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_List_lengthTRAux___rarg(x_1, x_12);
lean_inc(x_13);
x_14 = l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(x_2, x_13, x_13, x_3);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 1);
x_16 = l_List_reverse___rarg(x_14);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Expr_getAppFn(x_1);
x_20 = l_Lean_Expr_constLevels_x21(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_2);
x_21 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_getUElimPos_x3f(x_20, x_2, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_24 = l_Lean_Meta_isLevelDefEq(x_2, x_3, x_14, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_17, x_25);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_53; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
x_53 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__3;
x_27 = x_53;
goto block_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_8, 0);
lean_inc(x_54);
lean_dec(x_8);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Expr_getAppNumArgsAux(x_1, x_55);
x_57 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__5(x_9, x_10, x_11);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_12);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_22);
x_59 = lean_apply_1(x_54, x_58);
x_27 = x_59;
goto block_52;
}
block_52:
{
uint8_t x_28; lean_object* x_29; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_26, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_dec(x_26);
x_46 = 0;
x_28 = x_46;
x_29 = x_45;
goto block_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_dec(x_26);
lean_inc(x_7);
x_48 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_7, x_14, x_15, x_16, x_17, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_49);
lean_dec(x_49);
x_28 = x_51;
x_29 = x_50;
goto block_41;
}
block_41:
{
if (x_28 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Match_mkMatcher___lambda__1(x_4, x_5, x_6, x_1, x_27, x_30, x_14, x_15, x_16, x_17, x_29);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_1);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_33 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_7, x_36, x_14, x_15, x_16, x_17, x_29);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_Match_mkMatcher___lambda__1(x_4, x_5, x_6, x_1, x_27, x_38, x_14, x_15, x_16, x_17, x_39);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
return x_40;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_24);
if (x_60 == 0)
{
return x_24;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_24, 0);
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_24);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_20 = l_Lean_Meta_Match_mkMatcherAuxDefinition(x_1, x_2, x_3, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
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
x_46 = lean_st_ref_get(x_18, x_22);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = 0;
x_25 = x_51;
x_26 = x_50;
goto block_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
lean_inc(x_9);
x_53 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_9, x_15, x_16, x_17, x_18, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_25 = x_56;
x_26 = x_55;
goto block_45;
}
block_45:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_24, x_10, x_11, x_12, x_13, x_27, x_15, x_16, x_17, x_18, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = l_Lean_Expr_getAppFn(x_23);
x_30 = l_Lean_Expr_constLevels_x21(x_29);
lean_inc(x_8);
x_31 = l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__6(x_30, x_8);
x_32 = l_Lean_MessageData_ofList(x_31);
lean_dec(x_31);
x_33 = l_Lean_Meta_Match_mkMatcher___lambda__4___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Meta_Match_mkMatcher___lambda__4___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_4);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_4);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_9);
x_41 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_9, x_40, x_15, x_16, x_17, x_18, x_26);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_24, x_10, x_11, x_12, x_13, x_42, x_15, x_16, x_17, x_18, x_43);
lean_dec(x_42);
return x_44;
}
}
}
else
{
uint8_t x_57; 
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
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcher value: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkMatcher___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ntype: ");
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
x_30 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__2;
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
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
lean_inc(x_11);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkMatcher___spec__2(x_46, x_47, x_11);
x_49 = l_Array_append___rarg(x_44, x_48);
x_50 = 0;
x_51 = 1;
x_52 = 1;
lean_inc(x_49);
x_53 = l_Lean_Meta_mkForallFVars(x_49, x_1, x_50, x_51, x_52, x_12, x_13, x_14, x_15, x_41);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_mkLambdaFVars(x_49, x_21, x_50, x_51, x_52, x_12, x_13, x_14, x_15, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_77 = lean_st_ref_get(x_15, x_58);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 3);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get_uint8(x_79, sizeof(void*)*1);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_59 = x_50;
x_60 = x_81;
goto block_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
lean_inc(x_8);
x_83 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_8, x_12, x_13, x_14, x_15, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
x_59 = x_86;
x_60 = x_85;
goto block_76;
}
block_76:
{
if (x_59 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
x_62 = l_Lean_Meta_Match_mkMatcher___lambda__4(x_4, x_54, x_57, x_5, x_6, x_7, x_40, x_24, x_8, x_46, x_47, x_11, x_9, x_61, x_12, x_13, x_14, x_15, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc(x_57);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_57);
x_64 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__4;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Meta_Match_mkMatcher___lambda__5___closed__6;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_54);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_54);
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_withAlts_loop___rarg___closed__14;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_8);
x_72 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_8, x_71, x_12, x_13, x_14, x_15, x_60);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_Match_mkMatcher___lambda__4(x_4, x_54, x_57, x_5, x_6, x_7, x_40, x_24, x_8, x_46, x_47, x_11, x_9, x_73, x_12, x_13, x_14, x_15, x_74);
return x_75;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_54);
lean_dec(x_40);
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
x_87 = !lean_is_exclusive(x_56);
if (x_87 == 0)
{
return x_56;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_56, 0);
x_89 = lean_ctor_get(x_56, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_56);
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
lean_dec(x_49);
lean_dec(x_40);
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
x_91 = !lean_is_exclusive(x_53);
if (x_91 == 0)
{
return x_53;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_53, 0);
x_93 = lean_ctor_get(x_53, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_53);
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
x_95 = !lean_is_exclusive(x_35);
if (x_95 == 0)
{
return x_35;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_35, 0);
x_97 = lean_ctor_get(x_35, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_35);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
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
x_37 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_7, x_10, x_11, x_12, x_13, x_36);
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
x_25 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_7, x_24, x_10, x_11, x_12, x_13, x_17);
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
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_14, x_9, x_10, x_11, x_12, x_35);
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
x_24 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_14, x_23, x_9, x_10, x_11, x_12, x_16);
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
lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
lean_inc(x_6);
x_12 = l_Lean_mkSort(x_6);
x_13 = 0;
x_14 = 1;
x_15 = 1;
lean_inc(x_1);
x_16 = l_Lean_Meta_mkForallFVars(x_1, x_12, x_13, x_14, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkMatcher___lambda__8), 13, 7);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_6);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_17);
x_20 = l_Lean_Meta_Match_mkMatcher___lambda__9___closed__2;
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_20, x_21, x_17, x_19, x_7, x_8, x_9, x_10, x_18);
return x_22;
}
else
{
uint8_t x_23; 
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
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldAux___at_Lean_Meta_Match_mkMatcher___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkMatcher___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Match_mkMatcher___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
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
_start:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_21 = l_Lean_Meta_Match_mkMatcher___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
return x_21;
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
_start:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_21 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_22 = l_Lean_Meta_Match_mkMatcher___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
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
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_LocalContext_getFVar_x21(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
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
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_1);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__2(x_16, x_18, x_19, x_1);
x_21 = lean_array_get_size(x_3);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_toPattern___spec__2(x_22, x_19, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_array_to_list(lean_box(0), x_20);
x_27 = lean_array_to_list(lean_box(0), x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_array_to_list(lean_box(0), x_20);
x_33 = lean_array_to_list(lean_box(0), x_30);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_20);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_12);
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
x_19 = lean_usize_add(x_3, x_18);
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
x_24 = lean_usize_add(x_3, x_23);
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
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_infer_type(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_15, x_17, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_13, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_8 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5(x_9, x_10, x_1, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__1), 7, 0);
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
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__4;
x_9 = 0;
x_10 = 1;
x_11 = 1;
x_12 = l_Lean_Meta_mkForallFVars(x_1, x_8, x_9, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_Match_getMkMatcherInputInContext___lambda__3___closed__2;
x_12 = l_Lean_mkConst(x_11, x_10);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_2, x_12, x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_8);
return x_16;
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
lean_dec(x_3);
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
lean_dec(x_4);
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
x_11 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(x_10, x_5, x_6, x_7, x_8, x_9);
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
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_3, x_1, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_mkLambdaFVars(x_2, x_14, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
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
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
lean_dec(x_5);
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
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_12, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_inc(x_6);
x_19 = lean_array_to_list(lean_box(0), x_6);
lean_inc(x_18);
x_20 = l_Lean_mkConst(x_18, x_19);
x_21 = lean_ctor_get(x_3, 3);
lean_inc(x_21);
lean_inc(x_21);
x_22 = l_Lean_mkAppN(x_20, x_21);
lean_inc(x_16);
x_23 = l_Lean_mkApp(x_22, x_16);
lean_inc(x_4);
x_24 = l_Lean_mkAppN(x_23, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_24);
x_25 = l_Lean_Meta_check(x_24, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_24);
x_27 = l_Lean_Meta_isTypeCorrect(x_24, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_MatcherApp_addArg___lambda__2___closed__2;
x_32 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_31, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_MatcherApp_addArg___lambda__1(x_24, x_3, x_5, x_18, x_6, x_21, x_16, x_4, x_38, x_7, x_8, x_9, x_10, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_44; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_15, 0);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_15);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
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
x_21 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_20, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_12053_(lean_object* x_1) {
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MVarRenaming(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseValues(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Match(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_GeneralizeTelescope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MVarRenaming(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseValues(builtin, lean_io_mk_world());
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
l_Lean_Meta_Match_State_used___default = _init_l_Lean_Meta_Match_State_used___default();
lean_mark_persistent(l_Lean_Meta_Match_State_used___default);
l_Lean_Meta_Match_State_counterExamples___default = _init_l_Lean_Meta_Match_State_counterExamples___default();
lean_mark_persistent(l_Lean_Meta_Match_State_counterExamples___default);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__1);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__2 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__2();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__2);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__3);
l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4 = _init_l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processSkipInaccessible___spec__3___closed__4);
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
l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1 = _init_l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___spec__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processAsPattern___closed__2);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__1 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__1);
l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__2 = _init_l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processVariable___spec__2___closed__2);
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
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__1 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__1();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__1);
l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__2 = _init_l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__2();
lean_mark_persistent(l_List_filterMapM_loop___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___spec__10___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__1___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor___lambda__2___closed__2);
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
l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__1 = _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__1);
l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__2 = _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__2);
l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__3 = _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__3);
l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__4 = _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___lambda__2___closed__4);
l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__1 = _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__1();
lean_mark_persistent(l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__1);
l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__2 = _init_l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__2();
lean_mark_persistent(l_Array_mapIdxM_map___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processValue___spec__10___closed__2);
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
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_checkVarDeps___closed__2);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___spec__2___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__1);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__2);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__3 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__3);
l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__4 = _init_l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_process_tryToProcess___closed__4);
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
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__1 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__1();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__1);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__2 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__2();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__2);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__3 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__3();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__3);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__4 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__4();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__4);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__5 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__5();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__5);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__6 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__6();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338____closed__6);
if (builtin) {res = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9338_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Match_bootstrap_genMatcherCode = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Match_bootstrap_genMatcherCode);
lean_dec_ref(res);
}l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__1 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__1();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__1);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__2 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__2();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__2);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__3 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__3();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__3);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__4 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__4();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__4);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__5 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__5();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__5);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__6 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__6();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__6);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__7 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__7();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__7);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__8 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__8();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__8);
l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__9 = _init_l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__9();
lean_mark_persistent(l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364____closed__9);
if (builtin) {res = l_Lean_Meta_Match_initFn____x40_Lean_Meta_Match_Match___hyg_9364_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Match_matcherExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Match_matcherExt);
lean_dec_ref(res);
}l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__1 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__1();
l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__2 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Meta_Match_mkMatcherAuxDefinition___spec__5___closed__1);
l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1 = _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__2___closed__1);
l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__1 = _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__1);
l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__2 = _init_l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkMatcherAuxDefinition___lambda__4___closed__2);
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
l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_getMkMatcherInputInContext___spec__5___closed__1);
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
res = l_Lean_Meta_initFn____x40_Lean_Meta_Match_Match___hyg_12053_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
