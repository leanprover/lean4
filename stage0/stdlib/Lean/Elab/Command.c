// Lean compiler output
// Module: Lean.Elab.Command
// Imports: Init Lean.ResolveName Lean.Elab.Log Lean.Elab.Term Lean.Elab.Binders Lean.Elab.SyntheticMVars Lean.Elab.DeclModifiers
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
lean_object* l_Lean_Elab_Command_State_scopes___default___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_withLogging___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_expandDeclId___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSection(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__3;
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__3___closed__1;
extern lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFnsAux___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
extern lean_object* l_Lean_KeyedDeclsAttribute_KeyedDeclsAttribute_inhabited___closed__1;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_elabOpen___closed__5;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Command_withNamespace(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_scopes___default___closed__2;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_expandDeclId___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_Command_elabSection___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
extern lean_object* l_Lean_Core_Lean_CoreM___instance__1___closed__1;
lean_object* l_Lean_Elab_Command_setOption___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEval___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__4;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___closed__3;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__6;
lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_getScope___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3;
lean_object* l_Lean_Elab_Command_elabExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2(lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3127____closed__3;
lean_object* l_Lean_Elab_Command_Context_macroStack___default;
lean_object* l_Lean_Elab_Command_modifyScope_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___closed__5;
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabSection___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withLogging___closed__2;
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Meta_synthInstance___at_Lean_Elab_Command_elabSynth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___boxed(lean_object*);
extern lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__1;
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Context_cmdPos___default;
lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen___closed__2;
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_currNamespace___default;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftEIO(lean_object*);
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_Command_elabCheck(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1;
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables___closed__3;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_object*);
extern lean_object* l_Lean_getMaxRecDepth___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__6(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3;
lean_object* l_Lean_Elab_Command_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_opts___default;
lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withLogging_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand_match__2(lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScopes___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__3;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__1;
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__4;
extern lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
lean_object* l_Lean_Elab_Command_State_messages___default;
lean_object* l_Lean_Elab_Command_Scope_inhabited;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabOpen___closed__3;
lean_object* l_Lean_Elab_Command_elabOpen(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3;
lean_object* l_Lean_Elab_Command_expandInCmd___closed__7;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1;
lean_object* l_Lean_Elab_Command_elabSynth___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Lean_Elab_Term___instance__1___closed__1;
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__3;
lean_object* l_Lean_Elab_Command_elabCheck___closed__3;
lean_object* l_Lean_Elab_Command_setOption___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand_match__4(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen___closed__6;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__3;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__5;
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabOpen___closed__4;
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__3;
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__3;
lean_object* l_Lean_Elab_Command_liftEIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_mkDeclName___rarg___closed__2;
extern lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2;
lean_object* l_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_Elab_Command_elabCheck___closed__2;
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabChoiceAux_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2;
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8(lean_object*);
lean_object* l_Lean_Elab_Command_Scope_varDecls___default;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_openDecls___default;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_evalTactic___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_Exception___instance__1___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
lean_object* l_Lean_Elab_Command_State_nextInstIdx___default;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3;
lean_object* l_Lean_Elab_Command_elabEval___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM_match__1(lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__2;
lean_object* l_Lean_Elab_Command_liftCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2;
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__5;
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setElabConfig(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__1;
lean_object* l_Lean_Elab_Command_elabSetOption_match__2(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1;
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_766_(lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035_(lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_State_ngen___default;
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5;
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1;
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1;
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM_match__2(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2;
lean_object* l_Lean_Elab_Command_getScopes(lean_object*);
extern lean_object* l_Lean_protectedExt;
lean_object* l_Lean_Elab_Command_elbChoice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Context_currRecDepth___default;
lean_object* l_Lean_Elab_Command_elabExport(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*);
extern lean_object* l_IO_Error_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1;
lean_object* l_Lean_Elab_Command_liftCoreM_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_scopes___default;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
lean_object* l_Lean_Elab_Command_withLogging(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__5;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l_Lean_Meta_synthInstance___at_Lean_Elab_Command_elabSynth___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8;
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__2;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__2;
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__2;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Lean_Elab_Command_Scope_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_scopes___default___closed__3;
lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext___boxed(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__4;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2;
lean_object* l_Lean_Elab_Command_Scope_levelNames___default;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__2;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Command_withLogging_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4;
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabChoiceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Context_ref___default;
lean_object* l_Lean_Elab_Command_getMainModule___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog;
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_State_inhabited___closed__1;
lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__4;
extern lean_object* l_Bool_HasRepr___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Command_elabCommand_match__3(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
lean_object* l_Lean_Elab_Command_getScope(lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8;
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__3;
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabEval(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__1;
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption_match__1(lean_object*);
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_481____closed__3;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_resolveNamespace___rarg___lambda__1___closed__1;
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__1;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___closed__9;
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elbChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object*);
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__6;
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__1;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3;
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited;
lean_object* l_Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___closed__3;
extern lean_object* l_Lean_Elab_abortExceptionId;
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__3;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___closed__1;
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Context_currMacroScope___default;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__3;
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1;
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Lean_Elab_Command_setOption___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__4;
lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isMonad_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__5;
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__5;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabChoiceAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables(lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
extern lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__4;
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3;
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_expandInCmd___closed__8;
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_nextMacroScope___default;
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2;
lean_object* l_Lean_Elab_Command_expandInCmd___closed__4;
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isFreshInstanceName(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__1;
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_899____closed__1;
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6;
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3;
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_getScopes___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabChoiceAux_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__6;
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd_match__2(lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_getMacroStackOption(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__3;
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___closed__3;
lean_object* l_Lean_Elab_Command_elabNamespace___closed__1;
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__1;
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__2;
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
lean_object* l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2;
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__3;
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_Elab_Command_liftEIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__3(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Command_Scope_opts___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_levelNames___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_varDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Scope_inhabited___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_messages___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_scopes___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("root");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_scopes___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_scopes___default___closed__1;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_box(0);
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_scopes___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_scopes___default___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_scopes___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_scopes___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_nextMacroScope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Unhygienic_run___rarg___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_nextInstIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_ngen___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameGenerator_Inhabited___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_scopes___default___closed__1;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_box(0);
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Core_Lean_CoreM___instance__1___closed__1;
x_2 = l_Std_PersistentArray_empty___closed__1;
x_3 = l_Lean_Elab_Command_State_inhabited___closed__2;
x_4 = l_Lean_Unhygienic_run___rarg___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_NameGenerator_Inhabited___closed__3;
x_8 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_6);
lean_ctor_set(x_8, 6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_inhabited___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_mkState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_box(0);
x_5 = l_Lean_Elab_Command_State_scopes___default___closed__1;
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_box(0);
x_8 = l_Array_empty___closed__1;
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_4);
lean_ctor_set(x_9, 6, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = l_Lean_getMaxRecDepth(x_3);
lean_dec(x_3);
x_12 = l_Lean_Unhygienic_run___rarg___closed__1;
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_NameGenerator_Inhabited___closed__3;
x_15 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set(x_15, 6, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_currRecDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_cmdPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_macroStack___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_currMacroScope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_firstFrontendMacroScope;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_ref___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_25 = lean_apply_1(x_1, x_18);
x_26 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_22);
lean_ctor_set(x_26, 5, x_23);
lean_ctor_set(x_26, 6, x_24);
x_27 = lean_st_ref_set(x_3, x_26, x_7);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__4;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__6;
return x_1;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_StateRefT_x27_get___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_Scope_inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 2);
x_6 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__2___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__2;
return x_1;
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__2___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getRef(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_3, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_MetavarContext_Inhabited___closed__1;
x_16 = l_Lean_LocalContext_Inhabited___closed__2;
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_14);
x_18 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_MetavarContext_Inhabited___closed__1;
x_25 = l_Lean_LocalContext_Inhabited___closed__2;
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_23);
x_27 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__3___closed__1;
return x_1;
}
}
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 6);
lean_dec(x_8);
lean_ctor_set(x_4, 6, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 5, x_15);
lean_ctor_set(x_16, 6, x_2);
x_17 = lean_apply_3(x_3, x_16, x_5, x_6);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getRef___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__4___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__1;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_30; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_30 = l_Lean_Elab_getMacroStackOption(x_12);
lean_dec(x_12);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 1;
x_13 = x_31;
goto block_29;
}
else
{
uint8_t x_32; 
x_32 = 0;
x_13 = x_32;
goto block_29;
}
block_29:
{
if (x_13 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; 
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_9;
}
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = l_Lean_MessageData_ofList___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_List_foldl___main___at_Lean_Elab_addMacroStack___spec__1(x_16, x_25, x_2);
if (lean_is_scalar(x_9)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_9;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
else
{
lean_object* x_28; 
if (lean_is_scalar(x_9)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_9;
}
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
lean_inc(x_6);
x_7 = l_Lean_Elab_getBetterRef(x_1, x_6);
x_8 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1(x_9, x_6, x_3, x_4, x_10);
lean_dec(x_3);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_Lean_Elab_Command___instance__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_8);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_10);
lean_dec(x_6);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Elab_Command_mkMessageAux(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_liftCoreM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_liftCoreM_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM_match__2___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_st_ref_get(x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_2, x_47);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 6);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Lean_Unhygienic_run___rarg___closed__1;
x_53 = l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1;
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_mk_ref(x_54, x_48);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_56);
x_58 = lean_apply_3(x_1, x_49, x_56, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_st_ref_get(x_56, x_60);
lean_dec(x_56);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_63);
x_5 = x_65;
x_6 = x_64;
goto block_45;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_dec(x_58);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_66);
x_69 = lean_st_ref_get(x_56, x_67);
lean_dec(x_56);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_70);
x_5 = x_72;
x_6 = x_71;
goto block_45;
}
block_45:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_st_ref_take(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 6);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_10, 6, x_13);
lean_ctor_set(x_10, 0, x_12);
x_17 = lean_st_ref_set(x_3, x_10, x_11);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_10, 1);
x_31 = lean_ctor_get(x_10, 2);
x_32 = lean_ctor_get(x_10, 3);
x_33 = lean_ctor_get(x_10, 4);
x_34 = lean_ctor_get(x_10, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_35 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_13);
x_36 = lean_st_ref_set(x_3, x_35, x_11);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
lean_dec(x_7);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_38;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_42 = x_36;
} else {
 lean_dec_ref(x_36);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
lean_dec(x_7);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_liftCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftCoreM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = l_Lean_Elab_getBetterRef(x_2, x_4);
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = 2;
x_10 = l_Lean_Elab_Command_mkMessageAux(x_1, x_5, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_liftEIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftEIO___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftEIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftEIO___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_io_error_to_string(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_2, 6);
x_20 = lean_io_error_to_string(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_liftIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftIO___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftIO___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_io_error_to_string(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_2, 6);
x_20 = lean_io_error_to_string(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__6___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Command_getScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScope___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getScope___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getScope___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getScope(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScope___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__1;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__1;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__3;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__6;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__7___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_1, 4, x_16);
x_17 = lean_st_ref_take(x_3, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Std_PersistentArray_push___rarg(x_21, x_1);
lean_ctor_set(x_18, 1, x_22);
x_23 = lean_st_ref_set(x_3, x_18, x_19);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
x_36 = lean_ctor_get(x_18, 6);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_37 = l_Std_PersistentArray_push___rarg(x_31, x_1);
x_38 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_34);
lean_ctor_set(x_38, 5, x_35);
lean_ctor_set(x_38, 6, x_36);
x_39 = lean_st_ref_set(x_3, x_38, x_19);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_48 = lean_ctor_get(x_1, 3);
x_49 = lean_ctor_get(x_1, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_12);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_48);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*5, x_47);
x_53 = lean_st_ref_take(x_3, x_11);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_54, 6);
lean_inc(x_62);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 lean_ctor_release(x_54, 6);
 x_63 = x_54;
} else {
 lean_dec_ref(x_54);
 x_63 = lean_box(0);
}
x_64 = l_Std_PersistentArray_push___rarg(x_57, x_52);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 7, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_58);
lean_ctor_set(x_65, 3, x_59);
lean_ctor_set(x_65, 4, x_60);
lean_ctor_set(x_65, 5, x_61);
lean_ctor_set(x_65, 6, x_62);
x_66 = lean_st_ref_set(x_3, x_65, x_55);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
x_3 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
return x_1;
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_getCurrMacroScope(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_environment_main_module(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_environment_main_module(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Command_getMainModule(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getMainModule___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getMainModule___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getMainModule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getMainModule(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_ctor_set(x_6, 3, x_11);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 5);
lean_dec(x_15);
lean_ctor_set(x_2, 5, x_9);
x_16 = lean_apply_3(x_1, x_2, x_3, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_9);
lean_ctor_set(x_23, 6, x_22);
x_24 = lean_apply_3(x_1, x_23, x_3, x_13);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 2);
x_28 = lean_ctor_get(x_6, 3);
x_29 = lean_ctor_get(x_6, 4);
x_30 = lean_ctor_get(x_6, 5);
x_31 = lean_ctor_get(x_6, 6);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_28, x_32);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_31);
x_35 = lean_st_ref_set(x_3, x_34, x_7);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 6);
lean_inc(x_42);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_43 = x_2;
} else {
 lean_dec_ref(x_2);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 7, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_38);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_44, 5, x_28);
lean_ctor_set(x_44, 6, x_42);
x_45 = lean_apply_3(x_1, x_44, x_3, x_36);
return x_45;
}
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getCurrMacroScope___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2;
x_3 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
x_2 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElabAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3;
x_3 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5;
x_4 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7;
x_5 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_6 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9;
x_7 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3127____closed__3;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_766_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lean_indentD(x_7);
x_9 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFnsAux___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_12, x_4, x_5, x_6);
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_apply_4(x_14, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_27 = lean_nat_dec_eq(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_16);
lean_dec(x_17);
lean_inc(x_1);
x_28 = lean_st_ref_set(x_5, x_1, x_23);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_3 = x_15;
x_6 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
x_33 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_34 = lean_nat_dec_eq(x_33, x_32);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
lean_inc(x_1);
x_36 = lean_st_ref_set(x_5, x_1, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_3 = x_15;
x_6 = x_37;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_4, 4, x_10);
x_11 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
x_22 = lean_apply_3(x_3, x_21, x_5, x_6);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 3);
lean_dec(x_9);
lean_ctor_set(x_6, 3, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_1);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
lean_ctor_set(x_23, 6, x_22);
x_24 = lean_st_ref_set(x_3, x_23, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
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
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__2;
x_3 = l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__8___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 2);
lean_dec(x_8);
lean_ctor_set(x_4, 2, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 5);
x_15 = lean_ctor_get(x_4, 6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set(x_16, 6, x_15);
x_17 = lean_apply_3(x_3, x_16, x_5, x_6);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_Lean_Elab_Command___instance__1___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__5;
x_2 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__2;
x_3 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__6;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Command___instance__9___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withLogging_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Command_withLogging_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withLogging_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_2, x_4, x_5, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_FileMap_toPosition(x_13, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Command_getScope___rarg(x_5, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Command_getScope___rarg(x_5, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 4);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_15);
x_30 = l_String_splitAux___main___closed__1;
lean_inc(x_12);
x_31 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_3);
x_32 = lean_st_ref_take(x_5, x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_Std_PersistentArray_push___rarg(x_36, x_31);
lean_ctor_set(x_33, 1, x_37);
x_38 = lean_st_ref_set(x_5, x_33, x_34);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
x_47 = lean_ctor_get(x_33, 2);
x_48 = lean_ctor_get(x_33, 3);
x_49 = lean_ctor_get(x_33, 4);
x_50 = lean_ctor_get(x_33, 5);
x_51 = lean_ctor_get(x_33, 6);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_33);
x_52 = l_Std_PersistentArray_push___rarg(x_46, x_31);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_53, 5, x_50);
lean_ctor_set(x_53, 6, x_51);
x_54 = lean_st_ref_set(x_5, x_53, x_34);
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
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
x_62 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_2, x_4, x_5, x_9);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_FileMap_toPosition(x_61, x_59);
x_66 = lean_box(0);
x_67 = l_Lean_Elab_Command_getScope___rarg(x_5, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 3);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Elab_Command_getScope___rarg(x_5, x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 4);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_63);
x_77 = l_String_splitAux___main___closed__1;
lean_inc(x_60);
x_78 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_78, 0, x_60);
lean_ctor_set(x_78, 1, x_65);
lean_ctor_set(x_78, 2, x_66);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*5, x_3);
x_79 = lean_st_ref_take(x_5, x_73);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_80, 1);
x_84 = l_Std_PersistentArray_push___rarg(x_83, x_78);
lean_ctor_set(x_80, 1, x_84);
x_85 = lean_st_ref_set(x_5, x_80, x_81);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
x_94 = lean_ctor_get(x_80, 2);
x_95 = lean_ctor_get(x_80, 3);
x_96 = lean_ctor_get(x_80, 4);
x_97 = lean_ctor_get(x_80, 5);
x_98 = lean_ctor_get(x_80, 6);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_99 = l_Std_PersistentArray_push___rarg(x_93, x_78);
x_100 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_94);
lean_ctor_set(x_100, 3, x_95);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_97);
lean_ctor_set(x_100, 6, x_98);
x_101 = lean_st_ref_set(x_5, x_100, x_81);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_7, x_1, x_2, x_3, x_4, x_8);
lean_dec(x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 2;
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_5, x_6, x_7, x_2, x_3, x_4);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Elab_abortExceptionId;
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_InternalExceptionId_getName(x_9, x_4);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lean_Elab_logException___rarg___lambda__1___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = 2;
x_19 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_17, x_18, x_2, x_3, x_14);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_2, 6);
x_23 = lean_io_error_to_string(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_ctor_get(x_2, 6);
x_30 = lean_io_error_to_string(x_27);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_9);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_withLogging___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal exception ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_withLogging___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withLogging___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withLogging(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_6, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lean_Elab_abortExceptionId;
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_5);
x_15 = l_Lean_InternalExceptionId_getName(x_12, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = l_Lean_Elab_Command_withLogging___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = 2;
x_24 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_22, x_23, x_2, x_3, x_17);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_2, 6);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_io_error_to_string(x_26);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_ctor_get(x_2, 6);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_io_error_to_string(x_32);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_40);
return x_5;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_ctor_get(x_6, 0);
lean_inc(x_42);
lean_dec(x_6);
x_43 = l_Lean_Elab_abortExceptionId;
x_44 = lean_nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_InternalExceptionId_getName(x_42, x_41);
lean_dec(x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_49 = l_Lean_Elab_Command_withLogging___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = 2;
x_54 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_52, x_53, x_2, x_3, x_47);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_3);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_57 = x_45;
} else {
 lean_dec_ref(x_45);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_2, 6);
lean_inc(x_58);
lean_dec(x_2);
x_59 = lean_io_error_to_string(x_55);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_42);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_41);
return x_65;
}
}
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_899____closed__1;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3127____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabCommand_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabCommand_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_Elab_Command___instance__5___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_2, x_19, x_4, x_8);
return x_20;
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = 0;
x_8 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_11 = l_Lean_Elab_Command_elabCommand(x_10, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_2 = x_14;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 5);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_st_ref_take(x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 3);
x_22 = lean_nat_add(x_21, x_7);
lean_ctor_set(x_18, 3, x_22);
x_23 = lean_st_ref_set(x_5, x_18, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_14);
lean_inc(x_21);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_10);
lean_ctor_set(x_4, 5, x_21);
lean_ctor_set(x_4, 2, x_8);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
x_119 = l_Lean_nullKind;
x_120 = lean_name_eq(x_117, x_119);
lean_dec(x_117);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_118);
x_121 = lean_st_ref_get(x_5, x_24);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 2);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_124);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 2);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1;
x_128 = l_Lean_checkTraceOption(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
x_25 = x_123;
goto block_116;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_2);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_2);
x_130 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_127, x_129, x_4, x_5, x_123);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_25 = x_131;
goto block_116;
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11(x_118, x_132, x_4, x_5, x_24);
lean_dec(x_4);
lean_dec(x_118);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_134 = l_Lean_Elab_Tactic_evalTactic___lambda__1___closed__3;
x_135 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_134, x_4, x_5, x_24);
lean_dec(x_5);
return x_135;
}
block_116:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_56; lean_object* x_57; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_26 = lean_st_ref_get(x_5, x_25);
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
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_65 = lean_st_ref_get(x_5, x_28);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Command_getCurrMacroScope(x_4, x_5, x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_5, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 4);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_get(x_5, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 3);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_68);
x_80 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_80, 0, x_68);
x_81 = x_80;
x_82 = lean_environment_main_module(x_68);
lean_inc(x_8);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_70);
lean_ctor_set(x_83, 3, x_8);
lean_ctor_set(x_83, 4, x_75);
lean_inc(x_2);
x_84 = l_Lean_Elab_getMacros(x_30, x_2, x_83, x_79);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_29);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_st_ref_take(x_5, x_78);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_88, 3);
lean_dec(x_91);
lean_ctor_set(x_88, 3, x_86);
x_92 = lean_st_ref_set(x_5, x_88, x_89);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_85);
x_31 = x_94;
x_32 = x_93;
goto block_55;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_95 = lean_ctor_get(x_88, 0);
x_96 = lean_ctor_get(x_88, 1);
x_97 = lean_ctor_get(x_88, 2);
x_98 = lean_ctor_get(x_88, 4);
x_99 = lean_ctor_get(x_88, 5);
x_100 = lean_ctor_get(x_88, 6);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_88);
x_101 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_96);
lean_ctor_set(x_101, 2, x_97);
lean_ctor_set(x_101, 3, x_86);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set(x_101, 5, x_99);
lean_ctor_set(x_101, 6, x_100);
x_102 = lean_st_ref_set(x_5, x_101, x_89);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_85);
x_31 = x_104;
x_32 = x_103;
goto block_55;
}
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_84, 0);
lean_inc(x_105);
lean_dec(x_84);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
lean_inc(x_4);
x_110 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg(x_106, x_109, x_4, x_5, x_78);
lean_dec(x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_56 = x_111;
x_57 = x_112;
goto block_64;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(x_78);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_56 = x_114;
x_57 = x_115;
goto block_64;
}
}
block_55:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_33 = l_Lean_Elab_Command_commandElabAttribute;
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
x_35 = l_Lean_PersistentEnvExtension_getState___rarg(x_34, x_30);
lean_dec(x_30);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_2);
x_37 = l_Lean_Syntax_getKind(x_2);
x_38 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_27);
lean_dec(x_2);
x_39 = l_System_FilePath_dirName___closed__1;
x_40 = l_Lean_Name_toStringWithSep___main(x_39, x_37);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__2;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__4;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_46, x_4, x_5, x_32);
lean_dec(x_5);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(x_27, x_2, x_48, x_4, x_5, x_32);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_4);
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
lean_dec(x_31);
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_13);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_10);
lean_ctor_set(x_53, 1, x_11);
lean_ctor_set(x_53, 2, x_8);
lean_ctor_set(x_53, 3, x_12);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_21);
lean_ctor_set(x_53, 6, x_14);
x_54 = l_Lean_Elab_Command_elabCommand(x_50, x_53, x_5, x_32);
lean_dec(x_53);
return x_54;
}
}
block_64:
{
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_58; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_29)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_29;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
x_60 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_61 = lean_nat_dec_eq(x_60, x_59);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_29)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_29;
 lean_ctor_set_tag(x_62, 1);
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_56);
lean_dec(x_29);
x_63 = lean_box(0);
x_31 = x_63;
x_32 = x_57;
goto block_55;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_136 = lean_ctor_get(x_18, 0);
x_137 = lean_ctor_get(x_18, 1);
x_138 = lean_ctor_get(x_18, 2);
x_139 = lean_ctor_get(x_18, 3);
x_140 = lean_ctor_get(x_18, 4);
x_141 = lean_ctor_get(x_18, 5);
x_142 = lean_ctor_get(x_18, 6);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_18);
x_143 = lean_nat_add(x_139, x_7);
x_144 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_137);
lean_ctor_set(x_144, 2, x_138);
lean_ctor_set(x_144, 3, x_143);
lean_ctor_set(x_144, 4, x_140);
lean_ctor_set(x_144, 5, x_141);
lean_ctor_set(x_144, 6, x_142);
x_145 = lean_st_ref_set(x_5, x_144, x_19);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
lean_inc(x_14);
lean_inc(x_139);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_10);
lean_ctor_set(x_4, 5, x_139);
lean_ctor_set(x_4, 2, x_8);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_235 = lean_ctor_get(x_2, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_2, 1);
lean_inc(x_236);
x_237 = l_Lean_nullKind;
x_238 = lean_name_eq(x_235, x_237);
lean_dec(x_235);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
lean_dec(x_236);
x_239 = lean_st_ref_get(x_5, x_146);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_240, 2);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_242);
lean_dec(x_242);
x_244 = lean_ctor_get(x_243, 2);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1;
x_246 = l_Lean_checkTraceOption(x_244, x_245);
lean_dec(x_244);
if (x_246 == 0)
{
x_147 = x_241;
goto block_234;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_inc(x_2);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_2);
x_248 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_245, x_247, x_4, x_5, x_241);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_147 = x_249;
goto block_234;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_139);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_250 = lean_unsigned_to_nat(0u);
x_251 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11(x_236, x_250, x_4, x_5, x_146);
lean_dec(x_4);
lean_dec(x_236);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_139);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_252 = l_Lean_Elab_Tactic_evalTactic___lambda__1___closed__3;
x_253 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_252, x_4, x_5, x_146);
lean_dec(x_5);
return x_253;
}
block_234:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_178; lean_object* x_179; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_148 = lean_st_ref_get(x_5, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
x_187 = lean_st_ref_get(x_5, x_150);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Elab_Command_getCurrMacroScope(x_4, x_5, x_189);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_st_ref_get(x_5, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 4);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_st_ref_get(x_5, x_196);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 3);
lean_inc(x_201);
lean_dec(x_199);
lean_inc(x_190);
x_202 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_202, 0, x_190);
x_203 = x_202;
x_204 = lean_environment_main_module(x_190);
lean_inc(x_8);
x_205 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_192);
lean_ctor_set(x_205, 3, x_8);
lean_ctor_set(x_205, 4, x_197);
lean_inc(x_2);
x_206 = l_Lean_Elab_getMacros(x_152, x_2, x_205, x_201);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_151);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_st_ref_take(x_5, x_200);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 5);
lean_inc(x_216);
x_217 = lean_ctor_get(x_210, 6);
lean_inc(x_217);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 lean_ctor_release(x_210, 5);
 lean_ctor_release(x_210, 6);
 x_218 = x_210;
} else {
 lean_dec_ref(x_210);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 7, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_212);
lean_ctor_set(x_219, 1, x_213);
lean_ctor_set(x_219, 2, x_214);
lean_ctor_set(x_219, 3, x_208);
lean_ctor_set(x_219, 4, x_215);
lean_ctor_set(x_219, 5, x_216);
lean_ctor_set(x_219, 6, x_217);
x_220 = lean_st_ref_set(x_5, x_219, x_211);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_207);
x_153 = x_222;
x_154 = x_221;
goto block_177;
}
else
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_206, 0);
lean_inc(x_223);
lean_dec(x_206);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
lean_inc(x_4);
x_228 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg(x_224, x_227, x_4, x_5, x_200);
lean_dec(x_224);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_178 = x_229;
x_179 = x_230;
goto block_186;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(x_200);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_178 = x_232;
x_179 = x_233;
goto block_186;
}
}
block_177:
{
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_139);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_155 = l_Lean_Elab_Command_commandElabAttribute;
x_156 = lean_ctor_get(x_155, 2);
lean_inc(x_156);
x_157 = l_Lean_PersistentEnvExtension_getState___rarg(x_156, x_152);
lean_dec(x_152);
lean_dec(x_156);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
lean_inc(x_2);
x_159 = l_Lean_Syntax_getKind(x_2);
x_160 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_158, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_149);
lean_dec(x_2);
x_161 = l_System_FilePath_dirName___closed__1;
x_162 = l_Lean_Name_toStringWithSep___main(x_161, x_159);
x_163 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__2;
x_166 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__4;
x_168 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_168, x_4, x_5, x_154);
lean_dec(x_5);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_159);
x_170 = lean_ctor_get(x_160, 0);
lean_inc(x_170);
lean_dec(x_160);
x_171 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(x_149, x_2, x_170, x_4, x_5, x_154);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_4);
x_172 = lean_ctor_get(x_153, 0);
lean_inc(x_172);
lean_dec(x_153);
lean_inc(x_172);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_13);
x_175 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_175, 0, x_10);
lean_ctor_set(x_175, 1, x_11);
lean_ctor_set(x_175, 2, x_8);
lean_ctor_set(x_175, 3, x_12);
lean_ctor_set(x_175, 4, x_174);
lean_ctor_set(x_175, 5, x_139);
lean_ctor_set(x_175, 6, x_14);
x_176 = l_Lean_Elab_Command_elabCommand(x_172, x_175, x_5, x_154);
lean_dec(x_175);
return x_176;
}
}
block_186:
{
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_180; 
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_139);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_151)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_151;
 lean_ctor_set_tag(x_180, 1);
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_ctor_get(x_178, 0);
lean_inc(x_181);
x_182 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_183 = lean_nat_dec_eq(x_182, x_181);
lean_dec(x_181);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_139);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_151)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_151;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_179);
return x_184;
}
else
{
lean_object* x_185; 
lean_dec(x_178);
lean_dec(x_151);
x_185 = lean_box(0);
x_153 = x_185;
x_154 = x_179;
goto block_177;
}
}
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_254 = lean_ctor_get(x_4, 0);
x_255 = lean_ctor_get(x_4, 1);
x_256 = lean_ctor_get(x_4, 3);
x_257 = lean_ctor_get(x_4, 4);
x_258 = lean_ctor_get(x_4, 6);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_4);
x_259 = lean_st_ref_take(x_5, x_6);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_260, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_260, 3);
lean_inc(x_265);
x_266 = lean_ctor_get(x_260, 4);
lean_inc(x_266);
x_267 = lean_ctor_get(x_260, 5);
lean_inc(x_267);
x_268 = lean_ctor_get(x_260, 6);
lean_inc(x_268);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 lean_ctor_release(x_260, 4);
 lean_ctor_release(x_260, 5);
 lean_ctor_release(x_260, 6);
 x_269 = x_260;
} else {
 lean_dec_ref(x_260);
 x_269 = lean_box(0);
}
x_270 = lean_nat_add(x_265, x_7);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 7, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_262);
lean_ctor_set(x_271, 1, x_263);
lean_ctor_set(x_271, 2, x_264);
lean_ctor_set(x_271, 3, x_270);
lean_ctor_set(x_271, 4, x_266);
lean_ctor_set(x_271, 5, x_267);
lean_ctor_set(x_271, 6, x_268);
x_272 = lean_st_ref_set(x_5, x_271, x_261);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec(x_272);
lean_inc(x_258);
lean_inc(x_265);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_8);
lean_inc(x_255);
lean_inc(x_254);
x_274 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_274, 0, x_254);
lean_ctor_set(x_274, 1, x_255);
lean_ctor_set(x_274, 2, x_8);
lean_ctor_set(x_274, 3, x_256);
lean_ctor_set(x_274, 4, x_257);
lean_ctor_set(x_274, 5, x_265);
lean_ctor_set(x_274, 6, x_258);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_363 = lean_ctor_get(x_2, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_2, 1);
lean_inc(x_364);
x_365 = l_Lean_nullKind;
x_366 = lean_name_eq(x_363, x_365);
lean_dec(x_363);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
lean_dec(x_364);
x_367 = lean_st_ref_get(x_5, x_273);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get(x_368, 2);
lean_inc(x_370);
lean_dec(x_368);
x_371 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_370);
lean_dec(x_370);
x_372 = lean_ctor_get(x_371, 2);
lean_inc(x_372);
lean_dec(x_371);
x_373 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1;
x_374 = l_Lean_checkTraceOption(x_372, x_373);
lean_dec(x_372);
if (x_374 == 0)
{
x_275 = x_369;
goto block_362;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_inc(x_2);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_2);
x_376 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_373, x_375, x_274, x_5, x_369);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
x_275 = x_377;
goto block_362;
}
}
else
{
lean_object* x_378; lean_object* x_379; 
lean_dec(x_265);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_8);
lean_dec(x_2);
x_378 = lean_unsigned_to_nat(0u);
x_379 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11(x_364, x_378, x_274, x_5, x_273);
lean_dec(x_274);
lean_dec(x_364);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_265);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_8);
lean_dec(x_2);
x_380 = l_Lean_Elab_Tactic_evalTactic___lambda__1___closed__3;
x_381 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_380, x_274, x_5, x_273);
lean_dec(x_5);
return x_381;
}
block_362:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_306; lean_object* x_307; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_276 = lean_st_ref_get(x_5, x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_277, 0);
lean_inc(x_280);
x_315 = lean_st_ref_get(x_5, x_278);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lean_Elab_Command_getCurrMacroScope(x_274, x_5, x_317);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_st_ref_get(x_5, x_321);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_323, 4);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_st_ref_get(x_5, x_324);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_ctor_get(x_327, 3);
lean_inc(x_329);
lean_dec(x_327);
lean_inc(x_318);
x_330 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_330, 0, x_318);
x_331 = x_330;
x_332 = lean_environment_main_module(x_318);
lean_inc(x_8);
x_333 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set(x_333, 2, x_320);
lean_ctor_set(x_333, 3, x_8);
lean_ctor_set(x_333, 4, x_325);
lean_inc(x_2);
x_334 = l_Lean_Elab_getMacros(x_280, x_2, x_333, x_329);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_279);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_st_ref_take(x_5, x_328);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_338, 2);
lean_inc(x_342);
x_343 = lean_ctor_get(x_338, 4);
lean_inc(x_343);
x_344 = lean_ctor_get(x_338, 5);
lean_inc(x_344);
x_345 = lean_ctor_get(x_338, 6);
lean_inc(x_345);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 lean_ctor_release(x_338, 4);
 lean_ctor_release(x_338, 5);
 lean_ctor_release(x_338, 6);
 x_346 = x_338;
} else {
 lean_dec_ref(x_338);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(0, 7, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_340);
lean_ctor_set(x_347, 1, x_341);
lean_ctor_set(x_347, 2, x_342);
lean_ctor_set(x_347, 3, x_336);
lean_ctor_set(x_347, 4, x_343);
lean_ctor_set(x_347, 5, x_344);
lean_ctor_set(x_347, 6, x_345);
x_348 = lean_st_ref_set(x_5, x_347, x_339);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_335);
x_281 = x_350;
x_282 = x_349;
goto block_305;
}
else
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_334, 0);
lean_inc(x_351);
lean_dec(x_334);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_355 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_355, 0, x_354);
lean_inc(x_274);
x_356 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg(x_352, x_355, x_274, x_5, x_328);
lean_dec(x_352);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_306 = x_357;
x_307 = x_358;
goto block_314;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(x_328);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_306 = x_360;
x_307 = x_361;
goto block_314;
}
}
block_305:
{
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_265);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_8);
x_283 = l_Lean_Elab_Command_commandElabAttribute;
x_284 = lean_ctor_get(x_283, 2);
lean_inc(x_284);
x_285 = l_Lean_PersistentEnvExtension_getState___rarg(x_284, x_280);
lean_dec(x_280);
lean_dec(x_284);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
lean_inc(x_2);
x_287 = l_Lean_Syntax_getKind(x_2);
x_288 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_286, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_277);
lean_dec(x_2);
x_289 = l_System_FilePath_dirName___closed__1;
x_290 = l_Lean_Name_toStringWithSep___main(x_289, x_287);
x_291 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
x_293 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__2;
x_294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
x_295 = l_Lean_Elab_Command_elabCommand___lambda__1___closed__4;
x_296 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_296, x_274, x_5, x_282);
lean_dec(x_5);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_287);
x_298 = lean_ctor_get(x_288, 0);
lean_inc(x_298);
lean_dec(x_288);
x_299 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(x_277, x_2, x_298, x_274, x_5, x_282);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_280);
lean_dec(x_277);
lean_dec(x_274);
x_300 = lean_ctor_get(x_281, 0);
lean_inc(x_300);
lean_dec(x_281);
lean_inc(x_300);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_2);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_257);
x_303 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_303, 0, x_254);
lean_ctor_set(x_303, 1, x_255);
lean_ctor_set(x_303, 2, x_8);
lean_ctor_set(x_303, 3, x_256);
lean_ctor_set(x_303, 4, x_302);
lean_ctor_set(x_303, 5, x_265);
lean_ctor_set(x_303, 6, x_258);
x_304 = l_Lean_Elab_Command_elabCommand(x_300, x_303, x_5, x_282);
lean_dec(x_303);
return x_304;
}
}
block_314:
{
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_308; 
lean_dec(x_280);
lean_dec(x_277);
lean_dec(x_274);
lean_dec(x_265);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_279)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_279;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_309 = lean_ctor_get(x_306, 0);
lean_inc(x_309);
x_310 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_311 = lean_nat_dec_eq(x_310, x_309);
lean_dec(x_309);
if (x_311 == 0)
{
lean_object* x_312; 
lean_dec(x_280);
lean_dec(x_277);
lean_dec(x_274);
lean_dec(x_265);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_279)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_279;
 lean_ctor_set_tag(x_312, 1);
}
lean_ctor_set(x_312, 0, x_306);
lean_ctor_set(x_312, 1, x_307);
return x_312;
}
else
{
lean_object* x_313; 
lean_dec(x_306);
lean_dec(x_279);
x_313 = lean_box(0);
x_281 = x_313;
x_282 = x_307;
goto block_305;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_39 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_replaceRef(x_1, x_40);
lean_dec(x_40);
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_ctor_get(x_2, 4);
x_48 = lean_ctor_get(x_2, 5);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_46);
lean_ctor_set(x_49, 4, x_47);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_49, 6, x_42);
x_50 = lean_st_ref_get(x_3, x_41);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 4);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_nat_dec_eq(x_45, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(0);
lean_inc(x_3);
x_56 = l_Lean_Elab_Command_elabCommand___lambda__1(x_45, x_1, x_55, x_49, x_3, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_3);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_5 = x_57;
x_6 = x_58;
goto block_38;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_1);
x_59 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_60 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_59, x_49, x_3, x_52);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_5 = x_61;
x_6 = x_62;
goto block_38;
}
block_38:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_5, x_2, x_3, x_6);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_Elab_abortExceptionId;
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_InternalExceptionId_getName(x_8, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_Elab_Command_withLogging___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = 2;
x_20 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_18, x_19, x_2, x_3, x_13);
lean_dec(x_3);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_2, 6);
x_24 = lean_io_error_to_string(x_22);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_io_error_to_string(x_28);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___spec__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_elabCommand___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabCommand(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_3, 4, x_12);
x_13 = l_Lean_Elab_Command_elabCommand(x_7, x_3, x_4, x_8);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
x_19 = lean_ctor_get(x_3, 5);
x_20 = lean_ctor_get(x_3, 6);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
x_24 = l_Lean_Elab_Command_elabCommand(x_7, x_23, x_4, x_8);
lean_dec(x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_2);
x_4 = lean_ctor_get(x_3, 6);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_Exception___instance__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_inhabited___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_CommandElabM_inhabited___closed__1;
return x_2;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_CommandElabM_inhabited___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
lean_ctor_set_uint8(x_4, 4, x_2);
lean_ctor_set_uint8(x_4, 5, x_3);
lean_ctor_set_uint8(x_4, 6, x_1);
lean_ctor_set_uint8(x_4, 7, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2;
return x_1;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_4);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
lean_dec(x_5);
x_13 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_12);
lean_ctor_set(x_14, 6, x_8);
lean_ctor_set(x_14, 7, x_9);
lean_ctor_set_uint8(x_14, sizeof(void*)*8, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*8 + 1, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(x_1, x_8, x_5);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
x_11 = l_Lean_replaceRef(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getPos(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Elab_mkMessageCore(x_13, x_14, x_15, x_18, x_19);
lean_dec(x_14);
x_21 = l_Std_PersistentArray_push___rarg(x_5, x_20);
x_4 = x_17;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = 0;
x_25 = l_Lean_Elab_mkMessageCore(x_13, x_14, x_15, x_24, x_23);
lean_dec(x_14);
x_26 = l_Std_PersistentArray_push___rarg(x_5, x_25);
x_4 = x_17;
x_5 = x_26;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
x_11 = l_Lean_replaceRef(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getPos(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Elab_mkMessageCore(x_13, x_14, x_15, x_18, x_19);
lean_dec(x_14);
x_21 = l_Std_PersistentArray_push___rarg(x_5, x_20);
x_4 = x_17;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = 0;
x_25 = l_Lean_Elab_mkMessageCore(x_13, x_14, x_15, x_24, x_23);
lean_dec(x_14);
x_26 = l_Std_PersistentArray_push___rarg(x_5, x_25);
x_4 = x_17;
x_5 = x_26;
goto _start;
}
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(x_1, x_4, x_3);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(x_1, x_4, x_2);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_7, x_8, x_6, x_5);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM_match__2___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
x_2 = l_Lean_Elab_Term_setElabConfig(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 6);
lean_inc(x_12);
x_13 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(x_3, x_7, x_1);
x_14 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_3, x_7);
lean_dec(x_7);
x_15 = l_Lean_TraceState_Lean_Util_Trace___instance__2___closed__1;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_st_mk_ref(x_16, x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_70 = l_Lean_Meta_State_inhabited___closed__1;
x_71 = lean_st_mk_ref(x_70, x_19);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Term_Lean_Elab_Term___instance__1___closed__1;
x_75 = lean_st_mk_ref(x_74, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__2;
lean_inc(x_18);
lean_inc(x_72);
lean_inc(x_76);
x_79 = lean_apply_7(x_2, x_13, x_76, x_78, x_72, x_14, x_18, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_st_ref_get(x_76, x_81);
lean_dec(x_76);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_st_ref_get(x_72, x_85);
lean_dec(x_72);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_88);
x_20 = x_90;
x_21 = x_89;
goto block_69;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_dec(x_79);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_91);
x_94 = lean_st_ref_get(x_76, x_92);
lean_dec(x_76);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_st_ref_get(x_72, x_96);
lean_dec(x_72);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_99);
x_20 = x_101;
x_21 = x_100;
goto block_69;
}
block_69:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_22 = lean_st_ref_get(x_18, x_21);
lean_dec(x_18);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_st_ref_take(x_4, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 3);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_27, 2);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l_Std_PersistentArray_append___rarg(x_10, x_35);
lean_dec(x_35);
x_37 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_3, x_36, x_34);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_29, 6);
lean_dec(x_39);
x_40 = lean_ctor_get(x_29, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_29, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_29, 0);
lean_dec(x_42);
lean_ctor_set(x_29, 6, x_33);
lean_ctor_set(x_29, 3, x_32);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_31);
x_43 = lean_st_ref_set(x_4, x_29, x_30);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_26, 0);
lean_inc(x_46);
lean_dec(x_26);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
lean_dec(x_26);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_26, 0);
lean_inc(x_52);
lean_dec(x_26);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_ctor_get(x_26, 0);
lean_inc(x_54);
lean_dec(x_26);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_29, 2);
x_57 = lean_ctor_get(x_29, 4);
x_58 = lean_ctor_get(x_29, 5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_29);
x_59 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_37);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_32);
lean_ctor_set(x_59, 4, x_57);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set(x_59, 6, x_33);
x_60 = lean_st_ref_set(x_4, x_59, x_30);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_26, 0);
lean_inc(x_63);
lean_dec(x_26);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_62;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_26, 0);
lean_inc(x_67);
lean_dec(x_26);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_liftTermElabM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_7);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___lambda__1), 9, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Command_liftTermElabM___rarg(x_1, x_11, x_3, x_4, x_8);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_runTermElabM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_10, x_2, x_3, x_11);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = l_Lean_Elab_abortExceptionId;
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_5);
x_29 = l_Lean_InternalExceptionId_getName(x_26, x_24);
lean_dec(x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_30);
x_33 = l_Lean_Elab_Command_withLogging___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = 2;
x_38 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_36, x_37, x_2, x_3, x_31);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_29, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 0, x_45);
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_49);
return x_5;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
lean_dec(x_5);
x_51 = lean_ctor_get(x_10, 0);
lean_inc(x_51);
lean_dec(x_10);
x_52 = l_Lean_Elab_abortExceptionId;
x_53 = lean_nat_dec_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_InternalExceptionId_getName(x_51, x_50);
lean_dec(x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = l_Lean_Elab_Command_withLogging___closed__2;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = 2;
x_63 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_61, x_62, x_2, x_3, x_56);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_69 = x_54;
} else {
 lean_dec_ref(x_54);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
 lean_ctor_set_tag(x_71, 0);
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_50);
return x_73;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_3);
x_13 = l_Lean_Environment_registerNamespace(x_11, x_3);
x_14 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_14, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_8, 2, x_19);
lean_ctor_set(x_8, 0, x_13);
x_20 = lean_st_ref_set(x_5, x_8, x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 4);
x_29 = lean_ctor_get(x_14, 5);
x_30 = lean_ctor_get(x_14, 6);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_31 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_3);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
lean_ctor_set(x_31, 6, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_12);
lean_ctor_set(x_8, 2, x_32);
lean_ctor_set(x_8, 0, x_13);
x_33 = lean_st_ref_set(x_5, x_8, x_9);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
x_40 = lean_ctor_get(x_8, 2);
x_41 = lean_ctor_get(x_8, 3);
x_42 = lean_ctor_get(x_8, 4);
x_43 = lean_ctor_get(x_8, 5);
x_44 = lean_ctor_get(x_8, 6);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
lean_inc(x_3);
x_45 = l_Lean_Environment_registerNamespace(x_38, x_3);
x_46 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_40);
x_47 = lean_ctor_get(x_46, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 6);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 lean_ctor_release(x_46, 5);
 lean_ctor_release(x_46, 6);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 7, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_2);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_3);
lean_ctor_set(x_52, 4, x_48);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_50);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_41);
lean_ctor_set(x_54, 4, x_42);
lean_ctor_set(x_54, 5, x_43);
lean_ctor_set(x_54, 6, x_44);
x_55 = lean_st_ref_set(x_5, x_54, x_9);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_1(x_4, x_1);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid scope");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_1, x_2, x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_5, x_12);
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_1, x_10, x_16, x_4, x_5, x_15);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
x_21 = lean_name_mk_string(x_20, x_10);
x_22 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_1, x_10, x_21, x_4, x_5, x_19);
lean_dec(x_4);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
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
default: 
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3;
x_28 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_27, x_4, x_5, x_6);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namespace");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1;
x_6 = 1;
x_7 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabNamespace___closed__1;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
x_16 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1;
x_17 = 1;
x_18 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_16, x_17, x_15, x_2, x_3, x_4);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNamespace___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("section");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_elabSection___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabSection___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; uint8_t x_33; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_32 = l_Lean_nullKind___closed__2;
lean_inc(x_14);
x_33 = l_Lean_Syntax_isOfKind(x_14, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_15 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Syntax_getArgs(x_14);
x_36 = lean_array_get_size(x_35);
lean_dec(x_35);
x_37 = lean_nat_dec_eq(x_36, x_13);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_15 = x_38;
goto block_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Syntax_getArg(x_14, x_39);
lean_dec(x_14);
x_41 = l_Lean_identKind___closed__2;
lean_inc(x_40);
x_42 = l_Lean_Syntax_isOfKind(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_2);
x_43 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_44 = l_Lean_Syntax_getId(x_40);
lean_dec(x_40);
x_45 = l_Lean_Elab_Command_elabSection___closed__1;
x_46 = 0;
x_47 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_45, x_46, x_44, x_2, x_3, x_4);
return x_47;
}
}
}
block_31:
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_15);
x_16 = l_Lean_nullKind___closed__2;
lean_inc(x_14);
x_17 = l_Lean_Syntax_isOfKind(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 3);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Command_elabSection___closed__1;
x_29 = l_String_splitAux___main___closed__1;
x_30 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_28, x_29, x_27, x_2, x_3, x_26);
lean_dec(x_2);
return x_30;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSection(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSection___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_elabSection___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Command_getScopes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScopes___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getScopes___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScopes___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getScopes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getScopes(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 6);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean_string_dec_eq(x_8, x_14);
lean_dec(x_8);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_apply_1(x_3, x_1);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_apply_7(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_String_splitAux___main___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
case 1:
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_2(x_5, x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 6);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_box_usize(x_11);
x_21 = lean_apply_11(x_4, x_9, x_10, x_20, x_14, x_12, x_13, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
default: 
{
lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_apply_2(x_5, x_1, x_2);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1___rarg), 5, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_string_dec_eq(x_9, x_7);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
default: 
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabEnd_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabEnd_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabEnd_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name is missing");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name mismatch");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; 
x_7 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_8, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(x_12, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__6;
x_15 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_14, x_4, x_5, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', insufficient scopes");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getOptionalIdent_x3f(x_6);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_getScopes___rarg(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_8, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_8, 1);
lean_inc(x_75);
lean_dec(x_8);
x_9 = x_5;
x_10 = x_74;
x_11 = x_75;
goto block_73;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_7, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_8, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_8, 1);
lean_inc(x_78);
lean_dec(x_8);
x_79 = l_Lean_Name_getNumParts(x_76);
lean_dec(x_76);
x_9 = x_79;
x_10 = x_77;
x_11 = x_78;
goto block_73;
}
block_73:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_List_lengthAux___main___rarg(x_10, x_12);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_15 = lean_st_ref_take(x_3, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_16, 2);
x_20 = l_List_lengthAux___main___rarg(x_19, x_12);
x_21 = lean_nat_sub(x_20, x_5);
lean_dec(x_20);
x_22 = l_List_drop___main___rarg(x_21, x_19);
lean_dec(x_19);
lean_ctor_set(x_16, 2, x_22);
x_23 = lean_st_ref_set(x_3, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Command_elabEnd___closed__3;
x_26 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_25, x_2, x_3, x_24);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 2);
x_34 = lean_ctor_get(x_16, 3);
x_35 = lean_ctor_get(x_16, 4);
x_36 = lean_ctor_get(x_16, 5);
x_37 = lean_ctor_get(x_16, 6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_38 = l_List_lengthAux___main___rarg(x_33, x_12);
x_39 = lean_nat_sub(x_38, x_5);
lean_dec(x_38);
x_40 = l_List_drop___main___rarg(x_39, x_33);
lean_dec(x_33);
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_41, 6, x_37);
x_42 = lean_st_ref_set(x_3, x_41, x_17);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Elab_Command_elabEnd___closed__3;
x_45 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_44, x_2, x_3, x_43);
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
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_st_ref_take(x_3, x_11);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_51, 2);
x_55 = l_List_drop___main___rarg(x_9, x_54);
lean_dec(x_54);
lean_ctor_set(x_51, 2, x_55);
x_56 = lean_st_ref_set(x_3, x_51, x_52);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = l_Lean_Elab_Command_elabEnd___lambda__1(x_7, x_10, x_58, x_2, x_3, x_57);
lean_dec(x_10);
lean_dec(x_7);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
x_62 = lean_ctor_get(x_51, 2);
x_63 = lean_ctor_get(x_51, 3);
x_64 = lean_ctor_get(x_51, 4);
x_65 = lean_ctor_get(x_51, 5);
x_66 = lean_ctor_get(x_51, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_67 = l_List_drop___main___rarg(x_9, x_62);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
x_69 = lean_st_ref_set(x_3, x_68, x_52);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = l_Lean_Elab_Command_elabEnd___lambda__1(x_7, x_10, x_71, x_2, x_3, x_70);
lean_dec(x_10);
lean_dec(x_7);
return x_72;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_elabEnd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabEnd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("end");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1;
x_7 = 1;
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_6, x_7, x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_4);
x_10 = lean_apply_3(x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_14, 2);
x_18 = l_Lean_Name_getNumParts(x_1);
lean_dec(x_1);
x_19 = l_List_drop___main___rarg(x_18, x_17);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_19);
x_20 = lean_st_ref_set(x_4, x_14, x_15);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_14, 5);
x_31 = lean_ctor_get(x_14, 6);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_32 = l_Lean_Name_getNumParts(x_1);
lean_dec(x_1);
x_33 = l_List_drop___main___rarg(x_32, x_27);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_28);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_31);
x_35 = lean_st_ref_set(x_4, x_34, x_15);
lean_dec(x_4);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
return x_8;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Elab_Command_withNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withNamespace___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_modifyScope_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command.modifyScope");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Command_modifyScope___closed__1;
x_2 = l_Lean_Elab_Command_modifyScope___closed__2;
x_3 = lean_unsigned_to_nat(343u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_modifyScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Command_modifyScope___closed__3;
x_29 = lean_panic_fn(x_27, x_28);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_26);
x_31 = lean_st_ref_set(x_3, x_30, x_8);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_6, 2);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_apply_1(x_1, x_40);
lean_ctor_set(x_7, 0, x_41);
x_42 = lean_st_ref_set(x_3, x_6, x_36);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_apply_1(x_1, x_49);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_6, 2, x_52);
x_53 = lean_st_ref_set(x_3, x_6, x_36);
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
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
x_60 = lean_ctor_get(x_6, 3);
x_61 = lean_ctor_get(x_6, 4);
x_62 = lean_ctor_get(x_6, 5);
x_63 = lean_ctor_get(x_6, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_64 = lean_ctor_get(x_7, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_66 = x_7;
} else {
 lean_dec_ref(x_7);
 x_66 = lean_box(0);
}
x_67 = lean_apply_1(x_1, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_59);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_60);
lean_ctor_set(x_69, 4, x_61);
lean_ctor_set(x_69, 5, x_62);
lean_ctor_set(x_69, 6, x_63);
x_70 = lean_st_ref_set(x_3, x_69, x_36);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Command_getScope___rarg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 5);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getLevelNames___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getLevelNames___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getLevelNames___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getLevelNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getLevelNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Command_modifyScope___closed__3;
x_29 = lean_panic_fn(x_27, x_28);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_26);
x_31 = lean_st_ref_set(x_3, x_30, x_8);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_6, 2);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_7, 1);
x_42 = lean_ctor_get(x_7, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_36, 5);
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_36, 5, x_7);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_6, 2, x_45);
x_46 = lean_st_ref_set(x_3, x_6, x_37);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
x_55 = lean_ctor_get(x_36, 2);
x_56 = lean_ctor_get(x_36, 3);
x_57 = lean_ctor_get(x_36, 4);
x_58 = lean_ctor_get(x_36, 5);
x_59 = lean_ctor_get(x_36, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
lean_ctor_set(x_7, 1, x_58);
lean_ctor_set(x_7, 0, x_1);
x_60 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_7);
lean_ctor_set(x_60, 6, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_6, 2, x_61);
x_62 = lean_st_ref_set(x_3, x_6, x_37);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_36, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_36, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_36, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_36, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_36, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_36, 6);
lean_inc(x_74);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_75 = x_36;
} else {
 lean_dec_ref(x_36);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 7, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set(x_77, 5, x_76);
lean_ctor_set(x_77, 6, x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_6, 2, x_78);
x_79 = lean_st_ref_set(x_3, x_6, x_37);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_84 = lean_ctor_get(x_6, 0);
x_85 = lean_ctor_get(x_6, 1);
x_86 = lean_ctor_get(x_6, 3);
x_87 = lean_ctor_get(x_6, 4);
x_88 = lean_ctor_get(x_6, 5);
x_89 = lean_ctor_get(x_6, 6);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_6);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_91 = x_7;
} else {
 lean_dec_ref(x_7);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_36, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_36, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_36, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_36, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_36, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_36, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_36, 6);
lean_inc(x_98);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_99 = x_36;
} else {
 lean_dec_ref(x_36);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_97);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 7, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_94);
lean_ctor_set(x_101, 3, x_95);
lean_ctor_set(x_101, 4, x_96);
lean_ctor_set(x_101, 5, x_100);
lean_ctor_set(x_101, 6, x_98);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
x_103 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_103, 0, x_84);
lean_ctor_set(x_103, 1, x_85);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_86);
lean_ctor_set(x_103, 4, x_87);
lean_ctor_set(x_103, 5, x_88);
lean_ctor_set(x_103, 6, x_89);
x_104 = lean_st_ref_set(x_3, x_103, x_37);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_9, x_2, x_3, x_4);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 6);
lean_dec(x_11);
lean_ctor_set(x_2, 6, x_9);
x_12 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_5, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_5, x_2, x_3, x_14);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(x_5, x_2, x_3, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_24, 6, x_9);
x_25 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_5, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_5, x_24, x_3, x_27);
lean_dec(x_24);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(x_5, x_24, x_3, x_27);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addUnivLevel(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabChoiceAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_10 = l_Lean_Elab_Command_elabCommand(x_9, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_21 = lean_nat_dec_eq(x_20, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
lean_dec(x_2);
x_2 = x_31;
x_5 = x_25;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabChoiceAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elbChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Syntax_getArgs(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Elab_Command_elabChoiceAux(x_5, x_6, x_2, x_3, x_4);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elbChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elbChoice(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elbChoice___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_choiceKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Command_addUnivLevel(x_6, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabUniverse(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("universe");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverse___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
lean_inc(x_5);
x_14 = l_Lean_Elab_Command_addUnivLevel(x_11, x_5, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_13;
x_4 = x_15;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_box(0);
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_7, x_8, x_9, x_2, x_3, x_4);
lean_dec(x_7);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabUniverses(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("universes");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverses___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
lean_ctor_set(x_23, 6, x_22);
x_24 = lean_st_ref_set(x_3, x_23, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
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
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(4);
x_9 = lean_add_decl(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_2, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_head_x21___at_Lean_Elab_Command_Lean_Elab_Command___instance__2___spec__1(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_KernelException_toMessageData(x_10, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_17, x_1, x_2, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_19, x_1, x_2, x_6);
lean_dec(x_1);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabInitQuot___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabInitQuot(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("init_quot");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_2, x_4, x_5, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_FileMap_toPosition(x_13, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Command_getScope___rarg(x_5, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Command_getScope___rarg(x_5, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 4);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_15);
x_30 = l_String_splitAux___main___closed__1;
lean_inc(x_12);
x_31 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_3);
x_32 = lean_st_ref_take(x_5, x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_Std_PersistentArray_push___rarg(x_36, x_31);
lean_ctor_set(x_33, 1, x_37);
x_38 = lean_st_ref_set(x_5, x_33, x_34);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
x_47 = lean_ctor_get(x_33, 2);
x_48 = lean_ctor_get(x_33, 3);
x_49 = lean_ctor_get(x_33, 4);
x_50 = lean_ctor_get(x_33, 5);
x_51 = lean_ctor_get(x_33, 6);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_33);
x_52 = l_Std_PersistentArray_push___rarg(x_46, x_31);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_53, 5, x_50);
lean_ctor_set(x_53, 6, x_51);
x_54 = lean_st_ref_set(x_5, x_53, x_34);
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
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
x_62 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_Elab_Command___instance__3___spec__1(x_2, x_4, x_5, x_9);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_FileMap_toPosition(x_61, x_59);
x_66 = lean_box(0);
x_67 = l_Lean_Elab_Command_getScope___rarg(x_5, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 3);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Elab_Command_getScope___rarg(x_5, x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 4);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_63);
x_77 = l_String_splitAux___main___closed__1;
lean_inc(x_60);
x_78 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_78, 0, x_60);
lean_ctor_set(x_78, 1, x_65);
lean_ctor_set(x_78, 2, x_66);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*5, x_3);
x_79 = lean_st_ref_take(x_5, x_73);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_80, 1);
x_84 = l_Std_PersistentArray_push___rarg(x_83, x_78);
lean_ctor_set(x_80, 1, x_84);
x_85 = lean_st_ref_set(x_5, x_80, x_81);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
x_94 = lean_ctor_get(x_80, 2);
x_95 = lean_ctor_get(x_80, 3);
x_96 = lean_ctor_get(x_80, 4);
x_97 = lean_ctor_get(x_80, 5);
x_98 = lean_ctor_get(x_80, 6);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_99 = l_Std_PersistentArray_push___rarg(x_93, x_78);
x_100 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_94);
lean_ctor_set(x_100, 3, x_95);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_97);
lean_ctor_set(x_100, 6, x_98);
x_101 = lean_st_ref_set(x_5, x_100, x_81);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(x_7, x_1, x_2, x_3, x_4, x_8);
lean_dec(x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Command_logUnknownDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addClass___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Command_logUnknownDecl___closed__1;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = 2;
x_11 = l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(x_9, x_10, x_2, x_3, x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_logUnknownDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 4);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_ResolveName_resolveNamespace_x3f(x_8, x_12, x_17, x_1);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_13);
x_19 = l_System_FilePath_dirName___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_1);
x_21 = l_Lean_resolveNamespace___rarg___lambda__1___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_26, x_2, x_3, x_16);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_ctor_get(x_29, 4);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
x_32 = l_Lean_ResolveName_resolveNamespace_x3f(x_8, x_12, x_31, x_1);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = l_System_FilePath_dirName___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_1);
x_35 = l_Lean_resolveNamespace___rarg___lambda__1___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Char_HasRepr___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_40, x_2, x_3, x_30);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
return x_43;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_nat_dec_lt(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_array_fget(x_5, x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_17 = l_Lean_Syntax_getId(x_14);
lean_inc(x_17);
x_18 = l_Lean_Name_append___main(x_2, x_17);
lean_inc(x_4);
x_19 = l_Lean_Environment_contains(x_4, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_getRef(x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_replaceRef(x_14, x_21);
lean_dec(x_21);
lean_dec(x_14);
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
x_29 = lean_ctor_get(x_8, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_28);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_23);
x_31 = l_Lean_Elab_Command_logUnknownDecl(x_18, x_30, x_9, x_22);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_6 = x_16;
x_10 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_14);
x_34 = l_Lean_Name_append___main(x_3, x_17);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
x_6 = x_16;
x_7 = x_36;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_add_alias(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Command_elabExport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__2(x_1, x_2, x_3, x_11, x_14, x_16, x_15, x_5, x_6, x_10);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_6, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__3(x_24, x_18);
lean_ctor_set(x_21, 0, x_25);
x_26 = lean_st_ref_set(x_6, x_21, x_22);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
x_35 = lean_ctor_get(x_21, 2);
x_36 = lean_ctor_get(x_21, 3);
x_37 = lean_ctor_get(x_21, 4);
x_38 = lean_ctor_get(x_21, 5);
x_39 = lean_ctor_get(x_21, 6);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_40 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__3(x_33, x_18);
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 4, x_37);
lean_ctor_set(x_41, 5, x_38);
lean_ctor_set(x_41, 6, x_39);
x_42 = lean_st_ref_set(x_6, x_41, x_22);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'export', self export");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabExport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
lean_inc(x_2);
x_8 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_getScope___rarg(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_name_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Command_elabExport___lambda__1(x_1, x_9, x_14, x_16, x_2, x_3, x_13);
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_9);
x_18 = l_Lean_Elab_Command_elabExport___closed__3;
x_19 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_18, x_2, x_3, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
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
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabExport___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabExport(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("export");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabExport___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Command_modifyScope___closed__3;
x_29 = lean_panic_fn(x_27, x_28);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_26);
x_31 = lean_st_ref_set(x_3, x_30, x_8);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_6, 2);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_7, 1);
x_42 = lean_ctor_get(x_7, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_36, 4);
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_36, 4, x_7);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_6, 2, x_45);
x_46 = lean_st_ref_set(x_3, x_6, x_37);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
x_55 = lean_ctor_get(x_36, 2);
x_56 = lean_ctor_get(x_36, 3);
x_57 = lean_ctor_get(x_36, 4);
x_58 = lean_ctor_get(x_36, 5);
x_59 = lean_ctor_get(x_36, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
lean_ctor_set(x_7, 1, x_57);
lean_ctor_set(x_7, 0, x_1);
x_60 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_7);
lean_ctor_set(x_60, 5, x_58);
lean_ctor_set(x_60, 6, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_6, 2, x_61);
x_62 = lean_st_ref_set(x_3, x_6, x_37);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_36, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_36, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_36, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_36, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_36, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_36, 6);
lean_inc(x_74);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_75 = x_36;
} else {
 lean_dec_ref(x_36);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_72);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 7, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_73);
lean_ctor_set(x_77, 6, x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_6, 2, x_78);
x_79 = lean_st_ref_set(x_3, x_6, x_37);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_84 = lean_ctor_get(x_6, 0);
x_85 = lean_ctor_get(x_6, 1);
x_86 = lean_ctor_get(x_6, 3);
x_87 = lean_ctor_get(x_6, 4);
x_88 = lean_ctor_get(x_6, 5);
x_89 = lean_ctor_get(x_6, 6);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_6);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_91 = x_7;
} else {
 lean_dec_ref(x_7);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_36, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_36, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_36, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_36, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_36, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_36, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_36, 6);
lean_inc(x_98);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_99 = x_36;
} else {
 lean_dec_ref(x_36);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_96);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 7, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_94);
lean_ctor_set(x_101, 3, x_95);
lean_ctor_set(x_101, 4, x_100);
lean_ctor_set(x_101, 5, x_97);
lean_ctor_set(x_101, 6, x_98);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
x_103 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_103, 0, x_84);
lean_ctor_set(x_103, 1, x_85);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_86);
lean_ctor_set(x_103, 4, x_87);
lean_ctor_set(x_103, 5, x_88);
lean_ctor_set(x_103, 6, x_89);
x_104 = lean_st_ref_set(x_3, x_103, x_37);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
}
}
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_addOpenDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addOpenDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
lean_inc(x_5);
x_15 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_14, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_19, x_5, x_6, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_3 = x_13;
x_4 = x_21;
x_7 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_5);
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
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Syntax_inhabited;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_5, x_9, x_7, x_10, x_2, x_3, x_4);
lean_dec(x_9);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenSimple(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_5);
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_15 = l_Lean_Syntax_getId(x_12);
lean_inc(x_15);
x_16 = l_Lean_Name_append___main(x_2, x_15);
x_17 = lean_st_ref_get(x_7, x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Environment_contains(x_20, x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_15);
x_22 = l_Lean_Elab_Command_getRef(x_6, x_7, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_replaceRef(x_12, x_23);
lean_dec(x_23);
lean_dec(x_12);
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = lean_ctor_get(x_6, 4);
x_31 = lean_ctor_get(x_6, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_32 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_25);
x_33 = l_Lean_Elab_Command_logUnknownDecl(x_16, x_32, x_7, x_24);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_4 = x_14;
x_5 = x_34;
x_8 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_16);
x_38 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_37, x_6, x_7, x_19);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_4 = x_14;
x_5 = x_39;
x_8 = x_40;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Syntax_inhabited;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_6, x_5, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_5, x_11, x_15, x_7, x_16, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_11);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenOnly(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_fget(x_4, x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = l_Lean_Syntax_getId(x_13);
lean_inc(x_16);
x_17 = l_Lean_Name_append___main(x_2, x_16);
lean_inc(x_3);
x_18 = l_Lean_Environment_contains(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
x_19 = l_Lean_Elab_Command_getRef(x_7, x_8, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_replaceRef(x_13, x_20);
lean_dec(x_20);
lean_dec(x_13);
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
x_27 = lean_ctor_get(x_7, 4);
x_28 = lean_ctor_get(x_7, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_22);
x_30 = l_Lean_Elab_Command_logUnknownDecl(x_17, x_29, x_8, x_21);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_5 = x_15;
x_9 = x_31;
goto _start;
}
else
{
lean_object* x_33; 
lean_dec(x_17);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_6);
x_5 = x_15;
x_6 = x_33;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Syntax_inhabited;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_array_get(x_6, x_5, x_16);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_21 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_5, x_11, x_18, x_20, x_7, x_19, x_2, x_3, x_15);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_24, x_2, x_3, x_23);
lean_dec(x_2);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenHiding(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_5);
x_12 = lean_array_fget(x_3, x_4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getIdAt(x_12, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getIdAt(x_12, x_15);
x_17 = l_Lean_Name_append___main(x_1, x_14);
x_18 = lean_st_ref_get(x_7, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Environment_contains(x_21, x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
x_23 = l_Lean_Elab_Command_getRef(x_6, x_7, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_replaceRef(x_12, x_24);
lean_dec(x_24);
lean_dec(x_12);
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
x_29 = lean_ctor_get(x_6, 2);
x_30 = lean_ctor_get(x_6, 3);
x_31 = lean_ctor_get(x_6, 4);
x_32 = lean_ctor_get(x_6, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_33 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_26);
x_34 = l_Lean_Elab_Command_logUnknownDecl(x_17, x_33, x_7, x_25);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_37;
x_5 = x_35;
x_8 = x_36;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_17);
x_40 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_39, x_6, x_7, x_20);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_43;
x_5 = x_41;
x_8 = x_42;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Syntax_inhabited;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_6, x_5, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_11, x_13, x_15, x_7, x_16, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_11);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenRenaming(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openSimple");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_elabOpen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openOnly");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabOpen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_elabOpen___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabOpen___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openHiding");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabOpen___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_elabOpen___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_asNode(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = l_Lean_Elab_Command_elabOpen___closed__2;
x_10 = lean_name_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Command_elabOpen___closed__4;
x_12 = lean_name_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Command_elabOpen___closed__6;
x_14 = lean_name_eq(x_8, x_13);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabOpenRenaming(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabOpenHiding(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_8);
x_17 = l_Lean_Elab_Command_elabOpenOnly(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_8);
x_18 = l_Lean_Elab_Command_elabOpenSimple(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpen(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("open");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabOpen___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Command_modifyScope___closed__3;
x_29 = lean_panic_fn(x_27, x_28);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_26);
x_31 = lean_st_ref_set(x_3, x_30, x_8);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_6, 2);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_7, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_36, 6);
x_44 = lean_array_push(x_43, x_1);
lean_ctor_set(x_36, 6, x_44);
x_45 = lean_st_ref_set(x_3, x_6, x_37);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_36, 0);
x_53 = lean_ctor_get(x_36, 1);
x_54 = lean_ctor_get(x_36, 2);
x_55 = lean_ctor_get(x_36, 3);
x_56 = lean_ctor_get(x_36, 4);
x_57 = lean_ctor_get(x_36, 5);
x_58 = lean_ctor_get(x_36, 6);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_36);
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_59);
lean_ctor_set(x_7, 0, x_60);
x_61 = lean_st_ref_set(x_3, x_6, x_37);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
lean_dec(x_7);
x_67 = lean_ctor_get(x_36, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_36, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_36, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_36, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_36, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_36, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_36, 6);
lean_inc(x_73);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_74 = x_36;
} else {
 lean_dec_ref(x_36);
 x_74 = lean_box(0);
}
x_75 = lean_array_push(x_73, x_1);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 7, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_68);
lean_ctor_set(x_76, 2, x_69);
lean_ctor_set(x_76, 3, x_70);
lean_ctor_set(x_76, 4, x_71);
lean_ctor_set(x_76, 5, x_72);
lean_ctor_set(x_76, 6, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_6, 2, x_77);
x_78 = lean_st_ref_set(x_3, x_6, x_37);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_83 = lean_ctor_get(x_6, 0);
x_84 = lean_ctor_get(x_6, 1);
x_85 = lean_ctor_get(x_6, 3);
x_86 = lean_ctor_get(x_6, 4);
x_87 = lean_ctor_get(x_6, 5);
x_88 = lean_ctor_get(x_6, 6);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_6);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_90 = x_7;
} else {
 lean_dec_ref(x_7);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_36, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_36, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_36, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_36, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_36, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_36, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_36, 6);
lean_inc(x_97);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_98 = x_36;
} else {
 lean_dec_ref(x_36);
 x_98 = lean_box(0);
}
x_99 = lean_array_push(x_97, x_1);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 7, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_91);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_93);
lean_ctor_set(x_100, 3, x_94);
lean_ctor_set(x_100, 4, x_95);
lean_ctor_set(x_100, 5, x_96);
lean_ctor_set(x_100, 6, x_99);
if (lean_is_scalar(x_90)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_90;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
x_102 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_102, 0, x_83);
lean_ctor_set(x_102, 1, x_84);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_85);
lean_ctor_set(x_102, 4, x_86);
lean_ctor_set(x_102, 5, x_87);
lean_ctor_set(x_102, 6, x_88);
x_103 = lean_st_ref_set(x_3, x_102, x_37);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabVariable___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_mkOptionalNode___closed__2;
x_13 = lean_array_push(x_12, x_1);
x_14 = l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
x_15 = l_Lean_Elab_Term_elabBinders___rarg(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_13);
return x_15;
}
}
lean_object* l_Lean_Elab_Command_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_box(0);
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_9);
lean_dec(x_9);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__2___boxed), 9, 1);
lean_closure_set(x_12, 0, x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_inc(x_2);
x_14 = l_Lean_Elab_Command_liftTermElabM___rarg(x_7, x_13, x_2, x_3, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_6, x_2, x_3, x_15);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabVariable___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabVariable___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariable(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variable");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Command_modifyScope___closed__3;
x_29 = lean_panic_fn(x_27, x_28);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_26);
x_31 = lean_st_ref_set(x_3, x_30, x_8);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_6, 2);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_7, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_36, 6);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_44, x_43);
lean_ctor_set(x_36, 6, x_45);
x_46 = lean_st_ref_set(x_3, x_6, x_37);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
x_55 = lean_ctor_get(x_36, 2);
x_56 = lean_ctor_get(x_36, 3);
x_57 = lean_ctor_get(x_36, 4);
x_58 = lean_ctor_get(x_36, 5);
x_59 = lean_ctor_get(x_36, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_60, x_59);
x_62 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
lean_ctor_set(x_62, 6, x_61);
lean_ctor_set(x_7, 0, x_62);
x_63 = lean_st_ref_set(x_3, x_6, x_37);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
lean_dec(x_7);
x_69 = lean_ctor_get(x_36, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_36, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_36, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_36, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_36, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_36, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_36, 6);
lean_inc(x_75);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_76 = x_36;
} else {
 lean_dec_ref(x_36);
 x_76 = lean_box(0);
}
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_77, x_75);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 7, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_71);
lean_ctor_set(x_79, 3, x_72);
lean_ctor_set(x_79, 4, x_73);
lean_ctor_set(x_79, 5, x_74);
lean_ctor_set(x_79, 6, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_68);
lean_ctor_set(x_6, 2, x_80);
x_81 = lean_st_ref_set(x_3, x_6, x_37);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
x_88 = lean_ctor_get(x_6, 3);
x_89 = lean_ctor_get(x_6, 4);
x_90 = lean_ctor_get(x_6, 5);
x_91 = lean_ctor_get(x_6, 6);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
x_92 = lean_ctor_get(x_7, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_93 = x_7;
} else {
 lean_dec_ref(x_7);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_36, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_36, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_36, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_36, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_36, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_36, 5);
lean_inc(x_99);
x_100 = lean_ctor_get(x_36, 6);
lean_inc(x_100);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 lean_ctor_release(x_36, 6);
 x_101 = x_36;
} else {
 lean_dec_ref(x_36);
 x_101 = lean_box(0);
}
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_102, x_100);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_95);
lean_ctor_set(x_104, 2, x_96);
lean_ctor_set(x_104, 3, x_97);
lean_ctor_set(x_104, 4, x_98);
lean_ctor_set(x_104, 5, x_99);
lean_ctor_set(x_104, 6, x_103);
if (lean_is_scalar(x_93)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_93;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_92);
x_106 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_106, 0, x_86);
lean_ctor_set(x_106, 1, x_87);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_88);
lean_ctor_set(x_106, 4, x_89);
lean_ctor_set(x_106, 5, x_90);
lean_ctor_set(x_106, 6, x_91);
x_107 = lean_st_ref_set(x_3, x_106, x_37);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
x_13 = l_Lean_Elab_Term_elabBinders___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_elabVariables(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_st_ref_get(x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_10);
lean_dec(x_10);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___lambda__1___boxed), 9, 1);
lean_closure_set(x_13, 0, x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_inc(x_2);
x_15 = l_Lean_Elab_Command_liftTermElabM___rarg(x_8, x_14, x_2, x_3, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_7, x_2, x_3, x_16);
lean_dec(x_2);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabVariables___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariables(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("variables");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabVariables___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_elabTerm(x_1, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_21 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_15);
x_25 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_22);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
x_32 = 0;
x_33 = l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(x_31, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
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
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_check");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabCheck___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCheck___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_12);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___lambda__1___boxed), 9, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Command_elabCheck___closed__3;
lean_inc(x_2);
x_18 = l_Lean_Elab_Command_liftTermElabM___rarg(x_17, x_16, x_2, x_3, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_20);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_27);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabCheck___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabCheck(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_hasNoErrorMessages(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_failIfSucceeds_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected success");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3;
x_8 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_take(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_75; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = l_Std_PersistentArray_empty___closed__1;
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_46 = l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_75 = lean_apply_3(x_1, x_2, x_3, x_16);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_3, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_47 = x_80;
x_48 = x_79;
goto block_74;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec(x_75);
x_83 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_81, x_2, x_3, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = 0;
x_47 = x_85;
x_48 = x_84;
goto block_74;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_17 = x_86;
x_18 = x_87;
goto block_45;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_81);
x_88 = lean_ctor_get(x_75, 1);
lean_inc(x_88);
lean_dec(x_75);
x_89 = l_Lean_Elab_Command_failIfSucceeds___closed__4;
x_90 = 2;
x_91 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_89, x_90, x_2, x_3, x_88);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = 0;
x_47 = x_93;
x_48 = x_92;
goto block_74;
}
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_23);
x_25 = l_Std_PersistentArray_append___rarg(x_8, x_24);
lean_dec(x_24);
lean_ctor_set(x_20, 1, x_25);
x_26 = lean_st_ref_set(x_3, x_20, x_21);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_ctor_get(x_20, 2);
x_34 = lean_ctor_get(x_20, 3);
x_35 = lean_ctor_get(x_20, 4);
x_36 = lean_ctor_get(x_20, 5);
x_37 = lean_ctor_get(x_20, 6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_38 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_32);
x_39 = l_Std_PersistentArray_append___rarg(x_8, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set(x_40, 6, x_37);
x_41 = lean_st_ref_set(x_3, x_40, x_21);
lean_dec(x_3);
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
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
block_74:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_st_ref_take(x_3, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_50, 1);
x_54 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_53);
x_55 = l_Std_PersistentArray_append___rarg(x_8, x_54);
lean_dec(x_54);
lean_ctor_set(x_50, 1, x_55);
x_56 = lean_st_ref_set(x_3, x_50, x_51);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(x_47);
x_59 = lean_apply_4(x_46, x_58, x_2, x_3, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_60 = lean_ctor_get(x_50, 0);
x_61 = lean_ctor_get(x_50, 1);
x_62 = lean_ctor_get(x_50, 2);
x_63 = lean_ctor_get(x_50, 3);
x_64 = lean_ctor_get(x_50, 4);
x_65 = lean_ctor_get(x_50, 5);
x_66 = lean_ctor_get(x_50, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_50);
x_67 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_61);
x_68 = l_Std_PersistentArray_append___rarg(x_8, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set(x_69, 5, x_65);
lean_ctor_set(x_69, 6, x_66);
x_70 = lean_st_ref_set(x_3, x_69, x_51);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(x_47);
x_73 = lean_apply_4(x_46, x_72, x_2, x_3, x_71);
return x_73;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_147; 
x_94 = lean_ctor_get(x_10, 0);
x_95 = lean_ctor_get(x_10, 2);
x_96 = lean_ctor_get(x_10, 3);
x_97 = lean_ctor_get(x_10, 4);
x_98 = lean_ctor_get(x_10, 5);
x_99 = lean_ctor_get(x_10, 6);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_10);
x_100 = l_Std_PersistentArray_empty___closed__1;
x_101 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_95);
lean_ctor_set(x_101, 3, x_96);
lean_ctor_set(x_101, 4, x_97);
lean_ctor_set(x_101, 5, x_98);
lean_ctor_set(x_101, 6, x_99);
x_102 = lean_st_ref_set(x_3, x_101, x_11);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_125 = l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_147 = lean_apply_3(x_1, x_2, x_3, x_103);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_3, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox(x_150);
lean_dec(x_150);
x_126 = x_152;
x_127 = x_151;
goto block_146;
}
else
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_dec(x_147);
x_155 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_153, x_2, x_3, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = 0;
x_126 = x_157;
x_127 = x_156;
goto block_146;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_2);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
x_104 = x_158;
x_105 = x_159;
goto block_124;
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_153);
x_160 = lean_ctor_get(x_147, 1);
lean_inc(x_160);
lean_dec(x_147);
x_161 = l_Lean_Elab_Command_failIfSucceeds___closed__4;
x_162 = 2;
x_163 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_161, x_162, x_2, x_3, x_160);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = 0;
x_126 = x_165;
x_127 = x_164;
goto block_146;
}
}
block_124:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_106 = lean_st_ref_take(x_3, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 5);
lean_inc(x_114);
x_115 = lean_ctor_get(x_107, 6);
lean_inc(x_115);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 lean_ctor_release(x_107, 5);
 lean_ctor_release(x_107, 6);
 x_116 = x_107;
} else {
 lean_dec_ref(x_107);
 x_116 = lean_box(0);
}
x_117 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_110);
x_118 = l_Std_PersistentArray_append___rarg(x_8, x_117);
lean_dec(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 7, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_111);
lean_ctor_set(x_119, 3, x_112);
lean_ctor_set(x_119, 4, x_113);
lean_ctor_set(x_119, 5, x_114);
lean_ctor_set(x_119, 6, x_115);
x_120 = lean_st_ref_set(x_3, x_119, x_108);
lean_dec(x_3);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_104);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
block_146:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_128 = lean_st_ref_take(x_3, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 4);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 5);
lean_inc(x_136);
x_137 = lean_ctor_get(x_129, 6);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 lean_ctor_release(x_129, 6);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
x_139 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_132);
x_140 = l_Std_PersistentArray_append___rarg(x_8, x_139);
lean_dec(x_139);
if (lean_is_scalar(x_138)) {
 x_141 = lean_alloc_ctor(0, 7, 0);
} else {
 x_141 = x_138;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_134);
lean_ctor_set(x_141, 4, x_135);
lean_ctor_set(x_141, 5, x_136);
lean_ctor_set(x_141, 6, x_137);
x_142 = lean_st_ref_set(x_3, x_141, x_130);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_box(x_126);
x_145 = lean_apply_4(x_125, x_144, x_2, x_3, x_143);
return x_145;
}
}
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Command_failIfSucceeds___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Command_failIfSucceeds(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("check_failure");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckFailure), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_2);
x_9 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_eval_const(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_14);
return x_15;
}
}
lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_apply_1(x_1, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = 0;
x_18 = l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_io_error_to_string(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
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
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_io_error_to_string(x_32);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_10, 0, x_36);
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_io_error_to_string(x_37);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_9);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runEval");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = l_Lean_Elab_Term_resetMessageLog(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_elabTerm(x_1, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_mkSimpleThunk(x_17);
x_20 = 0;
x_21 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1;
x_25 = lean_name_mk_string(x_2, x_24);
x_26 = l_Lean_mkOptionalNode___closed__2;
x_27 = lean_array_push(x_26, x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isMonad_x3f___spec__1(x_25, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_10, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_36 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(0);
lean_inc(x_3);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_37);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_15);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_43);
x_44 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_9);
lean_inc(x_5);
x_46 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_5);
x_48 = l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_3);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_apply_8(x_35, x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_3);
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_dec(x_46);
x_63 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_43);
lean_dec(x_3);
x_68 = lean_ctor_get(x_44, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_44, 1);
lean_inc(x_69);
lean_dec(x_44);
x_70 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_29);
lean_dec(x_3);
x_75 = lean_ctor_get(x_36, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_36, 1);
lean_inc(x_76);
lean_dec(x_36);
x_77 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_76);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_28);
if (x_82 == 0)
{
return x_28;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_28, 0);
x_84 = lean_ctor_get(x_28, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_28);
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
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_22);
if (x_86 == 0)
{
return x_22;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_22, 0);
x_88 = lean_ctor_get(x_22, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_22);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_16);
if (x_90 == 0)
{
return x_16;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_16, 0);
x_92 = lean_ctor_get(x_16, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_16);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runMetaEval");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1;
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___closed__3;
lean_inc(x_2);
x_15 = lean_array_push(x_14, x_2);
lean_inc(x_4);
x_16 = lean_array_push(x_15, x_4);
x_17 = lean_array_push(x_16, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isMonad_x3f___spec__1(x_13, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkAppStx___closed__9;
x_22 = lean_array_push(x_21, x_2);
x_23 = lean_array_push(x_22, x_4);
x_24 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambdaAux___spec__1(x_23, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_2);
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
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("opts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Options");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__3;
lean_inc(x_1);
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l_Lean_mkConst(x_13, x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed), 11, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_3);
x_16 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__2;
x_17 = 0;
x_18 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_16, x_17, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = lean_apply_3(x_3, x_1, x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
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
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = 0;
x_20 = l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_io_error_to_string(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_io_error_to_string(x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_11);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_12, 0, x_41);
return x_12;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
x_44 = lean_io_error_to_string(x_42);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_inc(x_11);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("env");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Environment");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = l_Lean_Elab_Term_resetMessageLog(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_elabTerm(x_1, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__3;
lean_inc(x_2);
x_24 = lean_name_mk_string(x_2, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_mkConst(x_24, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4), 11, 3);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_17);
x_28 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__2;
x_29 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_28, x_29, x_26, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_10, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_31);
x_38 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_3);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_25);
lean_ctor_set(x_41, 2, x_39);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_15);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_44);
x_45 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_9);
lean_inc(x_5);
x_47 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_5);
x_49 = l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_3);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_36);
x_52 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(x_36, x_37, x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_37);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_37);
lean_dec(x_3);
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
lean_dec(x_47);
x_64 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_3);
x_69 = lean_ctor_get(x_45, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_45, 1);
lean_inc(x_70);
lean_dec(x_45);
x_71 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_3);
x_76 = lean_ctor_get(x_38, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 1);
lean_inc(x_77);
lean_dec(x_38);
x_78 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_76);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_30);
if (x_83 == 0)
{
return x_30;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_30, 0);
x_85 = lean_ctor_get(x_30, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_30);
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
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_21);
if (x_87 == 0)
{
return x_21;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_21, 0);
x_89 = lean_ctor_get(x_21, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
return x_16;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_16, 0);
x_93 = lean_ctor_get(x_16, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_16);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_eval");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MetaHasEval");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabEvalUnsafe___closed__5;
x_12 = l_Lean_Environment_contains(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_st_ref_get(x_3, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_14);
lean_dec(x_14);
x_17 = l_Lean_mkAppStx___closed__2;
x_18 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed), 11, 3);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
x_22 = l_Lean_Elab_Command_liftTermElabM___rarg(x_21, x_20, x_2, x_3, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_st_ref_get(x_3, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_24);
lean_dec(x_24);
x_27 = l_Lean_mkAppStx___closed__2;
x_28 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___boxed), 11, 3);
lean_closure_set(x_29, 0, x_6);
lean_closure_set(x_29, 1, x_27);
lean_closure_set(x_29, 2, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_30, 0, x_26);
lean_closure_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
x_32 = l_Lean_Elab_Command_liftTermElabM___rarg(x_31, x_30, x_2, x_3, x_25);
return x_32;
}
}
}
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabEvalUnsafe(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabEval___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lean_Exception___instance__1___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEval___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabEval(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eval");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_synthInstance___at_Lean_Elab_Command_elabSynth___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_elabTerm(x_1, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(x_22, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = 0;
x_29 = l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(x_27, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
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
lean_ctor_set(x_29, 0, x_18);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_synth_cmd");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSynth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSynth___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSynth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_12);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__1___boxed), 9, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Command_elabSynth___closed__3;
lean_inc(x_2);
x_18 = l_Lean_Elab_Command_liftTermElabM___rarg(x_17, x_16, x_2, x_3, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_20);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_27);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_synthInstance___at_Lean_Elab_Command_elabSynth___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_synthInstance___at_Lean_Elab_Command_elabSynth___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabSynth___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSynth(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synth");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_setOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_1, 2);
x_8 = l_Lean_getMaxRecDepth___closed__1;
x_9 = lean_string_dec_eq(x_6, x_8);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_1);
lean_dec(x_4);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box_usize(x_7);
x_16 = lean_apply_2(x_3, x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_8);
x_17 = lean_apply_2(x_4, x_1, x_2);
return x_17;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box_usize(x_7);
x_20 = lean_apply_2(x_3, x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set_usize(x_21, 2, x_7);
x_22 = lean_apply_2(x_4, x_21, x_2);
return x_22;
}
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
x_23 = lean_apply_2(x_4, x_1, x_2);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
x_24 = lean_apply_2(x_4, x_1, x_2);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Command_setOption_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_setOption_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_7, 2);
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_Command_modifyScope___closed__3;
x_14 = lean_panic_fn(x_12, x_13);
lean_ctor_set(x_7, 2, x_14);
x_15 = lean_st_ref_set(x_4, x_7, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 6);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_modifyScope___closed__3;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_24);
lean_ctor_set(x_31, 4, x_25);
lean_ctor_set(x_31, 5, x_26);
lean_ctor_set(x_31, 6, x_27);
x_32 = lean_st_ref_set(x_4, x_31, x_9);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_7, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_8, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_37, 2);
x_45 = l_Lean_KVMap_insertCore(x_44, x_1, x_2);
lean_ctor_set(x_37, 2, x_45);
x_46 = lean_st_ref_set(x_4, x_7, x_38);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
x_55 = lean_ctor_get(x_37, 2);
x_56 = lean_ctor_get(x_37, 3);
x_57 = lean_ctor_get(x_37, 4);
x_58 = lean_ctor_get(x_37, 5);
x_59 = lean_ctor_get(x_37, 6);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
x_60 = l_Lean_KVMap_insertCore(x_55, x_1, x_2);
x_61 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_56);
lean_ctor_set(x_61, 4, x_57);
lean_ctor_set(x_61, 5, x_58);
lean_ctor_set(x_61, 6, x_59);
lean_ctor_set(x_8, 0, x_61);
x_62 = lean_st_ref_set(x_4, x_7, x_38);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_dec(x_8);
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_37, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_37, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_37, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_37, 6);
lean_inc(x_74);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 lean_ctor_release(x_37, 6);
 x_75 = x_37;
} else {
 lean_dec_ref(x_37);
 x_75 = lean_box(0);
}
x_76 = l_Lean_KVMap_insertCore(x_70, x_1, x_2);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 7, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_71);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set(x_77, 5, x_73);
lean_ctor_set(x_77, 6, x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_7, 2, x_78);
x_79 = lean_st_ref_set(x_4, x_7, x_38);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_84 = lean_ctor_get(x_7, 0);
x_85 = lean_ctor_get(x_7, 1);
x_86 = lean_ctor_get(x_7, 3);
x_87 = lean_ctor_get(x_7, 4);
x_88 = lean_ctor_get(x_7, 5);
x_89 = lean_ctor_get(x_7, 6);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_7);
x_90 = lean_ctor_get(x_8, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_37, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_37, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_37, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_37, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_37, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_37, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_37, 6);
lean_inc(x_98);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 lean_ctor_release(x_37, 6);
 x_99 = x_37;
} else {
 lean_dec_ref(x_37);
 x_99 = lean_box(0);
}
x_100 = l_Lean_KVMap_insertCore(x_94, x_1, x_2);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 7, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_95);
lean_ctor_set(x_101, 4, x_96);
lean_ctor_set(x_101, 5, x_97);
lean_ctor_set(x_101, 6, x_98);
if (lean_is_scalar(x_91)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_91;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
x_103 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_103, 0, x_84);
lean_ctor_set(x_103, 1, x_85);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_86);
lean_ctor_set(x_103, 4, x_87);
lean_ctor_set(x_103, 5, x_88);
lean_ctor_set(x_103, 6, x_89);
x_104 = lean_st_ref_set(x_4, x_103, x_38);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
}
}
}
lean_object* l_Lean_Elab_Command_setOption___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(x_1, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_getMaxRecDepth___closed__1;
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_7);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_st_ref_take(x_5, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 4);
lean_dec(x_21);
lean_ctor_set(x_18, 4, x_16);
x_22 = lean_st_ref_set(x_5, x_18, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 3);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_35 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_16);
lean_ctor_set(x_35, 5, x_33);
lean_ctor_set(x_35, 6, x_34);
x_36 = lean_st_ref_set(x_5, x_35, x_19);
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
lean_object* x_41; 
lean_dec(x_2);
x_41 = lean_box(0);
lean_ctor_set(x_7, 0, x_41);
return x_7;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lean_getMaxRecDepth___closed__1;
x_45 = lean_string_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_st_ref_take(x_5, x_42);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 6);
lean_inc(x_57);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 lean_ctor_release(x_50, 5);
 lean_ctor_release(x_50, 6);
 x_58 = x_50;
} else {
 lean_dec_ref(x_50);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 7, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_48);
lean_ctor_set(x_59, 5, x_56);
lean_ctor_set(x_59, 6, x_57);
x_60 = lean_st_ref_set(x_5, x_59, x_51);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_42);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_7);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_7, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_7, 0, x_69);
return x_7;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_7, 1);
lean_inc(x_70);
lean_dec(x_7);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_7);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_7, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_7, 0, x_75);
return x_7;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_7, 1);
lean_inc(x_76);
lean_dec(x_7);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_setOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch at set_option");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_setOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_setOption___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_setOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_setOption___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_setOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_getOptionDecl(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_DataValue_sameCtor(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_Command_setOption___closed__3;
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_11, x_3, x_4, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Command_setOption___lambda__1(x_1, x_2, x_17, x_3, x_4, x_8);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_3, 6);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_io_error_to_string(x_20);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_ctor_get(x_3, 6);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_io_error_to_string(x_26);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_setOption___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_setOption___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_setOption(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Bool_HasRepr___closed__2;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
x_9 = l_Bool_HasRepr___closed__1;
x_10 = lean_string_dec_eq(x_6, x_9);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_apply_1(x_4, x_1);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_apply_1(x_3, x_5);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_apply_1(x_2, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabSetOption_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabSetOption_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption_match__3___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected set_option value ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSetOption___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isStrLit_x3f(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_numLitKind;
x_12 = l_Lean_Syntax_isNatLitAux(x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = l_Bool_HasRepr___closed__2;
x_15 = lean_string_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Bool_HasRepr___closed__1;
x_17 = lean_string_dec_eq(x_13, x_16);
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_7);
lean_inc(x_9);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_9);
x_19 = l_Lean_Elab_Command_elabSetOption___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = 2;
x_24 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_9, x_22, x_23, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_9);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_25 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
x_26 = l_Lean_Elab_Command_setOption(x_7, x_25, x_2, x_3, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
lean_dec(x_9);
x_27 = l_Lean_initFn____x40_Lean_Data_Options___hyg_481____closed__3;
x_28 = l_Lean_Elab_Command_setOption(x_7, x_27, x_2, x_3, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
lean_dec(x_7);
lean_inc(x_9);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_9);
x_30 = l_Lean_Elab_Command_elabSetOption___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 2;
x_35 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_9, x_33, x_34, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_9);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Elab_Command_setOption(x_7, x_37, x_2, x_3, x_4);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
lean_dec(x_10);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Elab_Command_setOption(x_7, x_40, x_2, x_3, x_4);
return x_41;
}
}
}
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSetOption(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("set_option");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Command_elabSection___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_expandInCmd___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInCmd___closed__2;
x_2 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabSection___closed__2;
x_2 = l_Lean_Elab_Command_expandInCmd___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_expandInCmd___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_expandInCmd___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandInCmd___closed__7;
x_2 = l___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_letBindRhss___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_2 = l_Lean_Elab_Command_expandInCmd___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_expandInCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Elab_Command_expandInCmd___closed__5;
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_Elab_Command_expandInCmd___closed__9;
x_12 = lean_array_push(x_10, x_11);
x_13 = l_Lean_nullKind___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
lean_object* l_Lean_Elab_Command_expandInCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandInCmd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("in");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandInCmd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Environment_contains(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_10);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_18, x_4, x_5, x_6);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_2, x_1);
lean_inc(x_2);
x_8 = l_Lean_Environment_contains(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_15, x_4, x_5, x_6);
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
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_8);
x_9 = l_Lean_Environment_contains(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(x_1, x_8, x_10, x_2, x_3, x_7);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_8);
lean_inc(x_1);
x_12 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_17, x_2, x_3, x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_28, x_2, x_3, x_7);
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
}
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
case 1:
{
lean_object* x_15; 
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_protectedExt;
lean_inc(x_2);
x_22 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_21, x_20, x_2);
x_23 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_22, x_3, x_4, x_19);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_st_ref_get(x_4, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkPrivateName(x_35, x_2);
lean_inc(x_36);
x_37 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_36, x_3, x_4, x_34);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_inc(x_2);
x_8 = l_Lean_Name_append___main(x_1, x_2);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_5);
x_10 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(x_9, x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(x_9);
if (lean_obj_tag(x_11) == 1)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_name_mk_string(x_15, x_14);
x_17 = l_Lean_Name_append___main(x_16, x_2);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_name_mk_string(x_22, x_21);
x_24 = l_Lean_Name_append___main(x_23, x_2);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__3;
x_29 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_28, x_5, x_6, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
return x_10;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_10);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_3);
x_7 = l_Lean_extractMacroScopes(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_isAtomic(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Elab_isFreshInstanceName(x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = l_Lean_Elab_mkDeclName___rarg___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_15, x_4, x_5, x_6);
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
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_1, x_3, x_2, x_21, x_4, x_5, x_6);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_1, x_3, x_2, x_23, x_4, x_5, x_6);
return x_24;
}
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_9, x_2, x_3, x_4);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_expandDeclId___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = l_Lean_Syntax_getId(x_11);
x_15 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_14, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_4);
x_3 = x_13;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_4);
x_18 = l_Lean_Elab_Command_getRef(x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_replaceRef(x_11, x_19);
lean_dec(x_19);
lean_dec(x_11);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_5, 6);
lean_dec(x_23);
lean_ctor_set(x_5, 6, x_21);
x_24 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__5(x_14, x_5, x_6, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_35 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_21);
x_36 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__5(x_14, x_35, x_6, x_20);
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
}
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_replaceRef(x_1, x_10);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 6);
lean_dec(x_14);
lean_ctor_set(x_6, 6, x_12);
x_15 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(x_2, x_3, x_4, x_6, x_7, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_5);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
x_33 = lean_ctor_get(x_6, 2);
x_34 = lean_ctor_get(x_6, 3);
x_35 = lean_ctor_get(x_6, 4);
x_36 = lean_ctor_get(x_6, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_37 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set(x_37, 6, x_12);
x_38 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(x_2, x_3, x_4, x_37, x_7, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_5);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
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
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Elab_expandDeclIdCore(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_isNone(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_10, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_empty___closed__1;
x_18 = l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(x_15, x_14, x_16, x_17);
lean_dec(x_14);
lean_inc(x_5);
x_19 = l_Array_iterateMAux___main___at_Lean_Elab_Command_expandDeclId___spec__6(x_10, x_18, x_16, x_2, x_5, x_6, x_7);
lean_dec(x_18);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_20, x_5, x_6, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_10);
x_27 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_2, x_5, x_6, x_7);
return x_27;
}
}
}
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Elab_Command_getScope___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(x_9, x_11, x_1, x_2, x_3, x_4, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_expandDeclId___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Command_expandDeclId___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_expandDeclId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_expandDeclId(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_ResolveName(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Command(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclModifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_Scope_opts___default = _init_l_Lean_Elab_Command_Scope_opts___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_opts___default);
l_Lean_Elab_Command_Scope_currNamespace___default = _init_l_Lean_Elab_Command_Scope_currNamespace___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_currNamespace___default);
l_Lean_Elab_Command_Scope_openDecls___default = _init_l_Lean_Elab_Command_Scope_openDecls___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_openDecls___default);
l_Lean_Elab_Command_Scope_levelNames___default = _init_l_Lean_Elab_Command_Scope_levelNames___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_levelNames___default);
l_Lean_Elab_Command_Scope_varDecls___default = _init_l_Lean_Elab_Command_Scope_varDecls___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_varDecls___default);
l_Lean_Elab_Command_Scope_inhabited___closed__1 = _init_l_Lean_Elab_Command_Scope_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Scope_inhabited___closed__1);
l_Lean_Elab_Command_Scope_inhabited = _init_l_Lean_Elab_Command_Scope_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_Scope_inhabited);
l_Lean_Elab_Command_State_messages___default = _init_l_Lean_Elab_Command_State_messages___default();
lean_mark_persistent(l_Lean_Elab_Command_State_messages___default);
l_Lean_Elab_Command_State_scopes___default___closed__1 = _init_l_Lean_Elab_Command_State_scopes___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default___closed__1);
l_Lean_Elab_Command_State_scopes___default___closed__2 = _init_l_Lean_Elab_Command_State_scopes___default___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default___closed__2);
l_Lean_Elab_Command_State_scopes___default___closed__3 = _init_l_Lean_Elab_Command_State_scopes___default___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default___closed__3);
l_Lean_Elab_Command_State_scopes___default = _init_l_Lean_Elab_Command_State_scopes___default();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default);
l_Lean_Elab_Command_State_nextMacroScope___default = _init_l_Lean_Elab_Command_State_nextMacroScope___default();
lean_mark_persistent(l_Lean_Elab_Command_State_nextMacroScope___default);
l_Lean_Elab_Command_State_nextInstIdx___default = _init_l_Lean_Elab_Command_State_nextInstIdx___default();
lean_mark_persistent(l_Lean_Elab_Command_State_nextInstIdx___default);
l_Lean_Elab_Command_State_ngen___default = _init_l_Lean_Elab_Command_State_ngen___default();
lean_mark_persistent(l_Lean_Elab_Command_State_ngen___default);
l_Lean_Elab_Command_State_inhabited___closed__1 = _init_l_Lean_Elab_Command_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__1);
l_Lean_Elab_Command_State_inhabited___closed__2 = _init_l_Lean_Elab_Command_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__2);
l_Lean_Elab_Command_State_inhabited___closed__3 = _init_l_Lean_Elab_Command_State_inhabited___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__3);
l_Lean_Elab_Command_State_inhabited = _init_l_Lean_Elab_Command_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited);
l_Lean_Elab_Command_Context_currRecDepth___default = _init_l_Lean_Elab_Command_Context_currRecDepth___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_currRecDepth___default);
l_Lean_Elab_Command_Context_cmdPos___default = _init_l_Lean_Elab_Command_Context_cmdPos___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_cmdPos___default);
l_Lean_Elab_Command_Context_macroStack___default = _init_l_Lean_Elab_Command_Context_macroStack___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_macroStack___default);
l_Lean_Elab_Command_Context_currMacroScope___default = _init_l_Lean_Elab_Command_Context_currMacroScope___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_currMacroScope___default);
l_Lean_Elab_Command_Context_ref___default = _init_l_Lean_Elab_Command_Context_ref___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_ref___default);
l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__2);
l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__3 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__3);
l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__4 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__4);
l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__5 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__5);
l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__6 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__1___closed__6);
l_Lean_Elab_Command_Lean_Elab_Command___instance__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__2___closed__2);
l_Lean_Elab_Command_Lean_Elab_Command___instance__2 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__2);
l_Lean_Elab_Command_Lean_Elab_Command___instance__3___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__3___closed__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__3 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__3);
l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__2);
l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__3 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__4___closed__3);
l_Lean_Elab_Command_Lean_Elab_Command___instance__4 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__4();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__4);
l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__2);
l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__3 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__3);
l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__4 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__4);
l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__5 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__5);
l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__6 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__7___closed__6);
l_Lean_Elab_Command_Lean_Elab_Command___instance__7 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__7();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__7);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__1);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__2 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__2);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__3 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__3);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__4 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__4);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__5 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__5);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__6 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__6);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__7 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__7);
l_Lean_Elab_Command_CommandElabM_monadLog = _init_l_Lean_Elab_Command_CommandElabM_monadLog();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4);
l_Lean_Elab_Command_CommandElabM_MonadQuotation = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_766_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_commandElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__2);
l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__3 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__3);
l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__4 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__8___closed__4);
l_Lean_Elab_Command_Lean_Elab_Command___instance__8 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__8();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__8);
l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__1);
l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__2);
l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__3 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__3);
l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__4 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__4);
l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__5 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__5);
l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__6 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__9___closed__6);
l_Lean_Elab_Command_Lean_Elab_Command___instance__9 = _init_l_Lean_Elab_Command_Lean_Elab_Command___instance__9();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Command___instance__9);
l_Lean_Elab_Command_withLogging___closed__1 = _init_l_Lean_Elab_Command_withLogging___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_withLogging___closed__1);
l_Lean_Elab_Command_withLogging___closed__2 = _init_l_Lean_Elab_Command_withLogging___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_withLogging___closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035____closed__1);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1035_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabCommand___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__1___closed__1);
l_Lean_Elab_Command_elabCommand___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__1___closed__2);
l_Lean_Elab_Command_elabCommand___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__1___closed__3);
l_Lean_Elab_Command_elabCommand___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabCommand___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___lambda__1___closed__4);
l_Lean_Elab_Command_CommandElabM_inhabited___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_inhabited___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__1);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__2 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___closed__1);
l_Lean_Elab_Command_elabNamespace___closed__1 = _init_l_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabNamespace___closed__1);
l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSection___closed__1 = _init_l_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSection___closed__1);
l_Lean_Elab_Command_elabSection___closed__2 = _init_l_Lean_Elab_Command_elabSection___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSection___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSection___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabSection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__1);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__2);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__3);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__4);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__5 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__5);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__6 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__6);
l_Lean_Elab_Command_elabEnd___closed__1 = _init_l_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__1);
l_Lean_Elab_Command_elabEnd___closed__2 = _init_l_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__2);
l_Lean_Elab_Command_elabEnd___closed__3 = _init_l_Lean_Elab_Command_elabEnd___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__3);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabEnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_modifyScope___closed__1 = _init_l_Lean_Elab_Command_modifyScope___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__1);
l_Lean_Elab_Command_modifyScope___closed__2 = _init_l_Lean_Elab_Command_modifyScope___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__2);
l_Lean_Elab_Command_modifyScope___closed__3 = _init_l_Lean_Elab_Command_modifyScope___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__3);
l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elbChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1);
l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__2);
l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_logUnknownDecl___closed__1 = _init_l_Lean_Elab_Command_logUnknownDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_logUnknownDecl___closed__1);
l_Lean_Elab_Command_elabExport___closed__1 = _init_l_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__1);
l_Lean_Elab_Command_elabExport___closed__2 = _init_l_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__2);
l_Lean_Elab_Command_elabExport___closed__3 = _init_l_Lean_Elab_Command_elabExport___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__3);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__1);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__2);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabExport(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabOpen___closed__1 = _init_l_Lean_Elab_Command_elabOpen___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabOpen___closed__1);
l_Lean_Elab_Command_elabOpen___closed__2 = _init_l_Lean_Elab_Command_elabOpen___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabOpen___closed__2);
l_Lean_Elab_Command_elabOpen___closed__3 = _init_l_Lean_Elab_Command_elabOpen___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabOpen___closed__3);
l_Lean_Elab_Command_elabOpen___closed__4 = _init_l_Lean_Elab_Command_elabOpen___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabOpen___closed__4);
l_Lean_Elab_Command_elabOpen___closed__5 = _init_l_Lean_Elab_Command_elabOpen___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabOpen___closed__5);
l_Lean_Elab_Command_elabOpen___closed__6 = _init_l_Lean_Elab_Command_elabOpen___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabOpen___closed__6);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabVariable___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabVariable___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabVariable___lambda__2___closed__1);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabVariable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1);
l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariables___closed__2);
l___regBuiltin_Lean_Elab_Command_elabVariables___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariables___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabVariables(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabCheck___closed__1 = _init_l_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__1);
l_Lean_Elab_Command_elabCheck___closed__2 = _init_l_Lean_Elab_Command_elabCheck___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__2);
l_Lean_Elab_Command_elabCheck___closed__3 = _init_l_Lean_Elab_Command_elabCheck___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__3);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2);
res = l___regBuiltin_Lean_Elab_Command_elabCheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3);
l_Lean_Elab_Command_failIfSucceeds___closed__1 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__1);
l_Lean_Elab_Command_failIfSucceeds___closed__2 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__2);
l_Lean_Elab_Command_failIfSucceeds___closed__3 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__3);
l_Lean_Elab_Command_failIfSucceeds___closed__4 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__4);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___closed__4 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__4);
l_Lean_Elab_Command_elabEvalUnsafe___closed__5 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__5);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__1);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__2);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabEval(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSynth___closed__1 = _init_l_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__1);
l_Lean_Elab_Command_elabSynth___closed__2 = _init_l_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__2);
l_Lean_Elab_Command_elabSynth___closed__3 = _init_l_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabSynth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_setOption___closed__1 = _init_l_Lean_Elab_Command_setOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__1);
l_Lean_Elab_Command_setOption___closed__2 = _init_l_Lean_Elab_Command_setOption___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__2);
l_Lean_Elab_Command_setOption___closed__3 = _init_l_Lean_Elab_Command_setOption___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__3);
l_Lean_Elab_Command_elabSetOption___closed__1 = _init_l_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__1);
l_Lean_Elab_Command_elabSetOption___closed__2 = _init_l_Lean_Elab_Command_elabSetOption___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandInCmd___closed__1 = _init_l_Lean_Elab_Command_expandInCmd___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__1);
l_Lean_Elab_Command_expandInCmd___closed__2 = _init_l_Lean_Elab_Command_expandInCmd___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__2);
l_Lean_Elab_Command_expandInCmd___closed__3 = _init_l_Lean_Elab_Command_expandInCmd___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__3);
l_Lean_Elab_Command_expandInCmd___closed__4 = _init_l_Lean_Elab_Command_expandInCmd___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__4);
l_Lean_Elab_Command_expandInCmd___closed__5 = _init_l_Lean_Elab_Command_expandInCmd___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__5);
l_Lean_Elab_Command_expandInCmd___closed__6 = _init_l_Lean_Elab_Command_expandInCmd___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__6);
l_Lean_Elab_Command_expandInCmd___closed__7 = _init_l_Lean_Elab_Command_expandInCmd___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__7);
l_Lean_Elab_Command_expandInCmd___closed__8 = _init_l_Lean_Elab_Command_expandInCmd___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__8);
l_Lean_Elab_Command_expandInCmd___closed__9 = _init_l_Lean_Elab_Command_expandInCmd___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__9);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3);
res = l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
