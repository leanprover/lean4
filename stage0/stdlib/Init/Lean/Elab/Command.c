// Lean compiler output
// Module: Init.Lean.Elab.Command
// Imports: Init.Lean.Elab.Alias Init.Lean.Elab.Log Init.Lean.Elab.ResolveName Init.Lean.Elab.Term Init.Lean.Elab.TermBinders Init.Lean.Elab.SynthesizeSyntheticMVars
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_5__elabCommandUsing___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4;
lean_object* l_Lean_Elab_Command_elabSection(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__3;
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__3;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3;
lean_object* l___private_Init_Lean_Elab_Command_8__updateState(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Command_withNamespace(lean_object*);
extern lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__6;
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1;
lean_object* l_Lean_Elab_Command_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1;
lean_object* l_Lean_Elab_Command_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace___main(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt___main(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Lean_Elab_Command_liftIOCore(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___main___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___main___spec__6(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTraceClass___closed__1;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO(lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withNamespace___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l___private_Init_Lean_Elab_Term_4__isCDot___closed__1;
lean_object* l___private_Init_Lean_Elab_Command_10__toCommandResult(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__2;
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_verboseOption___closed__3;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter;
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ElabFnTable_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2;
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__5;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_mkFreshKindAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5;
lean_object* l___private_Init_Lean_Elab_Command_9__getVarDecls(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__3;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__4;
lean_object* l___private_Init_Lean_Elab_Command_5__elabCommandUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr(lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___closed__2;
extern lean_object* l_Lean_getMaxRecDepth___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__11;
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_13__addNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__5;
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_14__throwParserCategoryAlreadyDefined___rarg___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Exception_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_Scope_inhabited;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__1;
extern lean_object* l_Lean_Meta_MetaHasEval___rarg___closed__4;
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption___closed__3;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabSynth___closed__2;
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables(lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__9;
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__3;
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd___closed__4;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__1;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__2;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabSynth(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2;
lean_object* l_Lean_Elab_Command_mkBuiltinCommandElabTable(lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3;
extern lean_object* l_Lean_Syntax_getKind___closed__4;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
lean_object* l_Lean_Elab_Command_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute___closed__4;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_Monad;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___closed__1;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Lean_Elab_Command_dbgTrace(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4;
lean_object* l_Lean_Elab_Command_elabEnd___closed__8;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
lean_object* l___private_Init_Lean_Elab_Command_4__modifyGetState(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_set__option___elambda__1___closed__2;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5;
lean_object* l_mkHashMap___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__2(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2;
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_15__checkEndHeader___main(lean_object*, lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3;
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab___closed__1;
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4;
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_1__ioErrorToMessage___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_14__checkAnonymousScope(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__3;
lean_object* l_Lean_KVMap_insertCore___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3;
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses(lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__1;
extern lean_object* l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScopes(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2;
uint8_t l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_builtinCommandElabTable;
lean_object* l___private_Init_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_15__checkEndHeader___boxed(lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withLogging(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2;
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Lean_Elab_Command_Scope_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__2;
lean_object* l_Lean_Elab_Command_liftIOCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__2;
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerAttributeImplBuilder___closed__2;
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd(lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1;
extern lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__3;
lean_object* l___private_Init_Lean_Elab_Command_13__addNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3;
size_t l_USize_land(size_t, size_t);
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__4;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog;
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l___private_Init_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___closed__2;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2;
extern lean_object* l_Bool_HasRepr___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_8__updateState___boxed(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand___main___closed__1;
lean_object* l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__1;
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_Command_getScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__6;
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__3;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__2;
lean_object* l_Lean_Elab_Command_withDeclId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__5;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withIncRecDepth(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2;
extern lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__2;
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot(lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___closed__2;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_9__getVarDecls___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__1;
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited;
lean_object* l_Lean_addMacroScopes(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getOpenDecls(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
lean_object* l_Lean_Elab_Command_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_getEnv(lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1;
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___closed__3;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4;
lean_object* l___private_Init_Lean_Elab_Command_6__mkTermContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__3;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_25__BuiltinParserAttribute_add___closed__2;
lean_object* l_Lean_Elab_Command_setOption___closed__3;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__5;
lean_object* l___private_Init_Lean_Elab_Command_4__modifyGetState___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7;
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7;
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_14__checkAnonymousScope___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3;
lean_object* l_Lean_Elab_Command_withDeclId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_11__addScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_variables___elambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth(lean_object*);
lean_object* l_Lean_Elab_Command_liftIOCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__2;
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__10;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_15__checkEndHeader___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_15__checkEndHeader(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__1;
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1;
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__1;
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
lean_object* l_Lean_Elab_Command_elabEnd___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_synth___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabSynth___closed__3;
lean_object* l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_10__toCommandResult___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__5;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1;
extern lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
extern lean_object* l_Lean_initAttr;
lean_object* l_Lean_Elab_Command_logTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2;
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
extern lean_object* l_Lean_Parser_regBuiltinCommandParserAttr___closed__3;
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation;
lean_object* l___private_Init_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_7__mkTermState___boxed(lean_object*);
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__2;
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_Elab_Command_Exception_inhabited;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2;
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Command_Scope_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Options_empty;
x_4 = lean_box(0);
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_Scope_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Scope_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("root");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_inhabited___closed__1;
x_3 = l_String_splitAux___main___closed__1;
x_4 = l_Lean_Options_empty;
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
x_7 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_1);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set(x_7, 6, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_State_inhabited___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtension_setState___closed__1;
x_2 = l_Lean_NameGenerator_Inhabited___closed__3;
x_3 = l_PersistentArray_empty___closed__3;
x_4 = l_Lean_Elab_Command_State_inhabited___closed__3;
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_inhabited___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_mkState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_box(0);
x_5 = l_Lean_Elab_Command_State_inhabited___closed__1;
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
x_12 = l_Lean_NameGenerator_Inhabited___closed__3;
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_13);
lean_ctor_set(x_14, 5, x_11);
return x_14;
}
}
lean_object* _init_l_Lean_Elab_Command_Exception_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Exception_inhabited___closed__1;
return x_1;
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
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_8);
lean_dec(x_8);
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
lean_dec(x_10);
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
lean_object* l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_Lean_Elab_getBetterRef(x_2, x_4);
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_addMacroStack(x_8, x_4);
x_10 = 2;
x_11 = l_Lean_Elab_Command_mkMessageAux(x_1, x_5, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_Command_1__ioErrorToMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_liftIOCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Command_liftIOCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftIOCore___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftIOCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftIOCore___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_3, x_1, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_3, x_1, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
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
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Command_2__getState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_io_ref_get(x_3, x_2);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_box(0);
x_12 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_16, x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_3__setState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_io_ref_set(x_4, x_1, x_3);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_box(0);
x_13 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_12, x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_17, x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_4__modifyGetState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Elab_Command_3__setState(x_9, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
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
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_4__modifyGetState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Command_4__modifyGetState___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Command_2__getState), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Command_3__setState), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Command_4__modifyGetState), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2;
x_3 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabCoreM_monadState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_2__getState(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
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
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Command_getScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_2__getState(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_6);
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
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
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
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Command_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Command_getOptions(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_MetavarContext_Inhabited___closed__1;
x_11 = l_Lean_LocalContext_Inhabited___closed__2;
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = l_Lean_MetavarContext_Inhabited___closed__1;
x_17 = l_Lean_LocalContext_Inhabited___closed__2;
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_14);
x_19 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
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
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = l_PersistentArray_push___rarg(x_8, x_1);
lean_ctor_set(x_5, 2, x_9);
x_10 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
uint8_t x_17; 
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
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
x_25 = lean_ctor_get(x_5, 4);
x_26 = lean_ctor_get(x_5, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_27 = l_PersistentArray_push___rarg(x_23, x_1);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_6);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
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
uint8_t x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_4);
if (x_38 == 0)
{
return x_4;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_addContext), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
x_3 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__11;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_addContext(x_1, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_2);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = l_String_splitAux___main___closed__1;
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_6);
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
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 0);
x_29 = l_Lean_FileMap_toPosition(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Elab_Command_addContext(x_1, x_4, x_5);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_box(0);
x_34 = l_String_splitAux___main___closed__1;
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_2);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = l_String_splitAux___main___closed__1;
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_29);
lean_dec(x_26);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_1, x_2, x_9, x_4, x_8);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 5);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l_Lean_Elab_getBetterRef(x_1, x_5);
x_7 = l_Lean_Elab_addMacroStack(x_2, x_5);
x_8 = 2;
x_9 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(x_7, x_8, x_6, x_3, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
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
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Command_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwError___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_throwError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_throwError___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
lean_inc(x_4);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_3, x_2, x_6, x_4, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
x_10 = l___private_Init_Lean_Elab_Command_2__getState(x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = l_PersistentArray_push___rarg(x_14, x_8);
lean_ctor_set(x_11, 2, x_15);
x_16 = l___private_Init_Lean_Elab_Command_3__setState(x_11, x_4, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
x_31 = lean_ctor_get(x_11, 4);
x_32 = lean_ctor_get(x_11, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_33 = l_PersistentArray_push___rarg(x_29, x_8);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = l___private_Init_Lean_Elab_Command_3__setState(x_34, x_4, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_42 = x_35;
} else {
 lean_dec_ref(x_35);
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
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
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
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_logTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_inc(x_4);
x_7 = l_Lean_Elab_Command_addContext(x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 0;
x_11 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_2, x_10, x_8, x_4, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logTrace___spec__2(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_logTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_logTrace(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_trace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Command_getOptions(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_10 = l_Lean_checkTraceOption(x_8, x_1);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_6);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_3, x_12);
x_14 = l_Lean_Elab_Command_logTrace(x_1, x_2, x_13, x_4, x_9);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
lean_inc(x_1);
x_17 = l_Lean_checkTraceOption(x_15, x_1);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_box(0);
x_21 = lean_apply_1(x_3, x_20);
x_22 = l_Lean_Elab_Command_logTrace(x_1, x_2, x_21, x_4, x_16);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_Command_trace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_trace(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwUnsupportedSyntax___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_throwUnsupportedSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_throwUnsupportedSyntax(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getCurrMacroScope(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getMainModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getEnv(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_environment_main_module(x_5);
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
x_9 = lean_environment_main_module(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_ctor_set(x_5, 4, x_10);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 6);
lean_dec(x_14);
lean_ctor_set(x_2, 6, x_8);
x_15 = lean_apply_2(x_1, x_2, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
x_20 = lean_ctor_get(x_2, 4);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_8);
x_23 = lean_apply_2(x_1, x_22, x_12);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_32, x_34);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
lean_inc(x_2);
x_37 = l___private_Init_Lean_Elab_Command_3__setState(x_36, x_2, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 5);
lean_inc(x_44);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_45 = x_2;
} else {
 lean_dec_ref(x_2);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 7, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 4, x_43);
lean_ctor_set(x_46, 5, x_44);
lean_ctor_set(x_46, 6, x_32);
x_47 = lean_apply_2(x_1, x_46, x_38);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_4);
if (x_52 == 0)
{
return x_4;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_4, 0);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getCurrMacroScope___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4() {
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
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__4;
return x_1;
}
}
lean_object* l_mkHashMap___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_mkBuiltinCommandElabTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_mkFreshKindAux___main___spec__3(x_17, x_18, x_3);
lean_dec(x_17);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(x_4, x_2);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(x_9, x_2);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* _init_l_Lean_Elab_Command_addBuiltinCommandElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin command elaborator, elaborator for '");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Command_builtinCommandElabTable;
x_6 = lean_io_ref_get(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(x_8, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_io_ref_get(x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_ref_reset(x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_ElabFnTable_insert___rarg(x_12, x_1, x_3);
x_17 = lean_io_ref_set(x_5, x_16, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_Elab_Command_addBuiltinCommandElab___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l___private_Init_Lean_Parser_Parser_14__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_32);
return x_6;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_35 = l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(x_33, x_1);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_io_ref_get(x_5, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_ref_reset(x_5, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Elab_ElabFnTable_insert___rarg(x_37, x_1, x_3);
x_42 = lean_io_ref_set(x_5, x_41, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
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
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_1);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_1);
x_53 = l_Lean_Elab_Command_addBuiltinCommandElab___closed__1;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l___private_Init_Lean_Parser_Parser_14__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_34);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_6);
if (x_59 == 0)
{
return x_6;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinCommandElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinCommandElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin command elaborator '");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2;
lean_inc(x_3);
x_6 = l_Lean_Name_append___main(x_5, x_3);
x_7 = lean_box(0);
x_8 = l_Lean_nameToExprAux___main(x_2);
lean_inc(x_3);
x_9 = l_Lean_nameToExprAux___main(x_3);
lean_inc(x_3);
x_10 = l_Lean_mkConst(x_3, x_7);
x_11 = l_Lean_Parser_declareBuiltinParser___closed__8;
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6;
x_17 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_14, x_14, x_15, x_16);
lean_dec(x_14);
x_18 = l_Lean_Parser_declareBuiltinParser___closed__7;
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_box(0);
x_21 = 0;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Options_empty;
x_25 = l_Lean_Environment_addAndCompile(x_1, x_24, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_6);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_3);
x_28 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l_Lean_initAttr;
x_36 = lean_box(0);
x_37 = l_Lean_ParametricAttribute_setParam___rarg(x_35, x_34, x_6, x_36);
x_38 = l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(x_37, x_4);
lean_dec(x_37);
return x_38;
}
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'builtinCommandElab', must be persistent");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected command elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `CommandElab` expected");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CommandElab");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_8, x_3);
x_10 = l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_24 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l___private_Init_Lean_Parser_Parser_25__BuiltinParserAttribute_add___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_ConstantInfo_type(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_mkAppStx___closed__1;
x_39 = lean_string_dec_eq(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_40 = lean_box(0);
x_14 = x_40;
goto block_23;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
x_42 = lean_string_dec_eq(x_36, x_41);
lean_dec(x_36);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_43 = lean_box(0);
x_14 = x_43;
goto block_23;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__1;
x_45 = lean_string_dec_eq(x_35, x_44);
lean_dec(x_35);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_46 = lean_box(0);
x_14 = x_46;
goto block_23;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__5;
x_48 = lean_string_dec_eq(x_34, x_47);
lean_dec(x_34);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_1);
x_49 = lean_box(0);
x_14 = x_49;
goto block_23;
}
else
{
lean_object* x_50; 
lean_dec(x_13);
x_50 = l_Lean_Elab_Command_declareBuiltinCommandElab(x_1, x_11, x_2, x_12);
return x_50;
}
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_51 = lean_box(0);
x_14 = x_51;
goto block_23;
}
}
else
{
lean_object* x_52; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_52 = lean_box(0);
x_14 = x_52;
goto block_23;
}
}
else
{
lean_object* x_53; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_53 = lean_box(0);
x_14 = x_53;
goto block_23;
}
}
else
{
lean_object* x_54; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_54 = lean_box(0);
x_14 = x_54;
goto block_23;
}
}
else
{
lean_object* x_55; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_55 = lean_box(0);
x_14 = x_55;
goto block_23;
}
}
else
{
lean_object* x_56; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_56 = lean_box(0);
x_14 = x_56;
goto block_23;
}
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_2);
x_17 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_13;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
else
{
uint8_t x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
return x_10;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCommandElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin command elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2;
x_2 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3;
x_3 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__2;
x_3 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
x_4 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__3;
x_5 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__3;
x_6 = l_Lean_Elab_Command_builtinCommandElabTable;
x_7 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_commandElabAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Elab_Command_commandElabAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Command_commandElabAttribute___closed__3;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_Elab_Term_termElabAttribute___closed__4;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__2;
x_2 = l_Lean_Elab_Command_commandElabAttribute___closed__4;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 5);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_nat_dec_eq(x_11, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_3, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_3, 0);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_11, x_25);
lean_dec(x_11);
lean_ctor_set(x_3, 3, x_26);
x_27 = lean_apply_2(x_2, x_3, x_7);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_11, x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_10);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_12);
lean_ctor_set(x_30, 5, x_13);
lean_ctor_set(x_30, 6, x_14);
x_31 = lean_apply_2(x_2, x_30, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_32 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_33 = l_Lean_Elab_Command_throwError___rarg(x_1, x_32, x_3, x_7);
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
}
else
{
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
return x_5;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Lean_Elab_Command_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withIncRecDepth___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withIncRecDepth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_withIncRecDepth___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Command_5__elabCommandUsing___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Lean_Syntax_prettyPrint(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofList___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Command_throwError___rarg(x_2, x_13, x_4, x_5);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_17 = lean_apply_3(x_15, x_2, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l___private_Init_Lean_Elab_Command_3__setState(x_1, x_4, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
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
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_5__elabCommandUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Command_5__elabCommandUsing___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_4, 5, x_9);
x_10 = lean_apply_2(x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set(x_20, 6, x_17);
x_21 = lean_apply_2(x_3, x_20, x_5);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_1);
x_9 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
x_24 = lean_ctor_get(x_5, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_1);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
x_26 = l___private_Init_Lean_Elab_Command_3__setState(x_25, x_2, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
return x_4;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1;
x_2 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getEnv), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__2), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwError), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwUnsupportedSyntax___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3;
x_2 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
x_3 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2;
x_4 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4;
x_5 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5;
x_6 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___main___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___main___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(x_4, x_2);
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
x_9 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_10 = l_Lean_Elab_Command_elabCommand___main(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabCommand___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_nat_dec_eq(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 6);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 5);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_10, x_24);
lean_dec(x_10);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_ctor_set(x_2, 3, x_25);
lean_inc(x_2);
x_26 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 4);
x_31 = lean_nat_add(x_30, x_24);
lean_ctor_set(x_27, 4, x_31);
x_32 = l___private_Init_Lean_Elab_Command_3__setState(x_27, x_2, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_30);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_9);
lean_ctor_set(x_34, 3, x_25);
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 5, x_12);
lean_ctor_set(x_34, 6, x_30);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_inc(x_161);
x_162 = l_Lean_nullKind;
x_163 = lean_name_eq(x_160, x_162);
lean_dec(x_160);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_161);
lean_inc(x_34);
x_164 = l_Lean_Elab_Command_getOptions(x_34, x_33);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Elab_Command_elabCommand___main___closed__1;
x_168 = l_Lean_checkTraceOption(x_165, x_167);
lean_dec(x_165);
if (x_168 == 0)
{
x_35 = x_166;
goto block_159;
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_inc(x_1);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_1);
lean_inc(x_34);
x_170 = l_Lean_Elab_Command_logTrace(x_167, x_1, x_169, x_34, x_166);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_35 = x_171;
goto block_159;
}
else
{
uint8_t x_172; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_170);
if (x_172 == 0)
{
return x_170;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_170, 0);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_170);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_164);
if (x_176 == 0)
{
return x_164;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_164, 0);
x_178 = lean_ctor_get(x_164, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_164);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_180 = lean_unsigned_to_nat(0u);
x_181 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_161, x_180, x_34, x_33);
lean_dec(x_161);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_182 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_183 = l_Lean_Elab_Command_throwError___rarg(x_1, x_182, x_34, x_33);
lean_dec(x_1);
return x_183;
}
block_159:
{
lean_object* x_36; 
lean_inc(x_34);
x_36 = l___private_Init_Lean_Elab_Command_2__getState(x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Command_commandElabAttribute;
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = l_Lean_PersistentEnvExtension_getState___rarg(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_1);
x_44 = l_Lean_Syntax_getKind(x_1);
x_45 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_43, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
lean_dec(x_37);
lean_inc(x_34);
x_46 = l_Lean_Elab_Command_getEnv(x_34, x_38);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_57; lean_object* x_58; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_74 = l_Lean_Elab_Command_getCurrMacroScope(x_34, x_48);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_34);
x_77 = l_Lean_Elab_Command_getEnv(x_34, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_34);
x_80 = l___private_Init_Lean_Elab_Command_2__getState(x_34, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_environment_main_module(x_78);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
lean_inc(x_1);
x_86 = l_Lean_Elab_getMacros(x_47, x_1, x_85, x_83);
lean_dec(x_47);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_34);
x_89 = l___private_Init_Lean_Elab_Command_2__getState(x_34, x_82);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_dec(x_93);
lean_ctor_set(x_90, 1, x_88);
lean_inc(x_34);
x_94 = l___private_Init_Lean_Elab_Command_3__setState(x_90, x_34, x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_34);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_50 = x_87;
x_51 = x_95;
goto block_56;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_87);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_57 = x_96;
x_58 = x_97;
goto block_73;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_90, 0);
x_99 = lean_ctor_get(x_90, 2);
x_100 = lean_ctor_get(x_90, 3);
x_101 = lean_ctor_get(x_90, 4);
x_102 = lean_ctor_get(x_90, 5);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_90);
x_103 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_88);
lean_ctor_set(x_103, 2, x_99);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_101);
lean_ctor_set(x_103, 5, x_102);
lean_inc(x_34);
x_104 = l___private_Init_Lean_Elab_Command_3__setState(x_103, x_34, x_91);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_34);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_50 = x_87;
x_51 = x_105;
goto block_56;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_87);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_57 = x_106;
x_58 = x_107;
goto block_73;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_108 = lean_ctor_get(x_89, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_89, 1);
lean_inc(x_109);
lean_dec(x_89);
x_57 = x_108;
x_58 = x_109;
goto block_73;
}
}
else
{
lean_object* x_110; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_110 = lean_ctor_get(x_86, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_86, 1);
lean_inc(x_111);
lean_dec(x_86);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_34);
x_113 = l___private_Init_Lean_Elab_Command_2__getState(x_34, x_82);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = !lean_is_exclusive(x_114);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_dec(x_117);
lean_ctor_set(x_114, 1, x_111);
lean_inc(x_34);
x_118 = l___private_Init_Lean_Elab_Command_3__setState(x_114, x_34, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_112);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_inc(x_34);
x_122 = l_Lean_Elab_Command_throwError___rarg(x_1, x_121, x_34, x_119);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_57 = x_123;
x_58 = x_124;
goto block_73;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_112);
x_125 = lean_ctor_get(x_118, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_118, 1);
lean_inc(x_126);
lean_dec(x_118);
x_57 = x_125;
x_58 = x_126;
goto block_73;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_114, 0);
x_128 = lean_ctor_get(x_114, 2);
x_129 = lean_ctor_get(x_114, 3);
x_130 = lean_ctor_get(x_114, 4);
x_131 = lean_ctor_get(x_114, 5);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_114);
x_132 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_111);
lean_ctor_set(x_132, 2, x_128);
lean_ctor_set(x_132, 3, x_129);
lean_ctor_set(x_132, 4, x_130);
lean_ctor_set(x_132, 5, x_131);
lean_inc(x_34);
x_133 = l___private_Init_Lean_Elab_Command_3__setState(x_132, x_34, x_115);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_112);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
lean_inc(x_34);
x_137 = l_Lean_Elab_Command_throwError___rarg(x_1, x_136, x_34, x_134);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_57 = x_138;
x_58 = x_139;
goto block_73;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_112);
x_140 = lean_ctor_get(x_133, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_133, 1);
lean_inc(x_141);
lean_dec(x_133);
x_57 = x_140;
x_58 = x_141;
goto block_73;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_112);
lean_dec(x_111);
x_142 = lean_ctor_get(x_113, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_113, 1);
lean_inc(x_143);
lean_dec(x_113);
x_57 = x_142;
x_58 = x_143;
goto block_73;
}
}
else
{
lean_object* x_144; 
lean_dec(x_86);
x_144 = lean_box(1);
x_57 = x_144;
x_58 = x_82;
goto block_73;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_47);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_145 = lean_ctor_get(x_80, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_80, 1);
lean_inc(x_146);
lean_dec(x_80);
x_57 = x_145;
x_58 = x_146;
goto block_73;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_75);
lean_dec(x_47);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_147 = lean_ctor_get(x_77, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_77, 1);
lean_inc(x_148);
lean_dec(x_77);
x_57 = x_147;
x_58 = x_148;
goto block_73;
}
block_56:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_12);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_7);
lean_ctor_set(x_54, 1, x_8);
lean_ctor_set(x_54, 2, x_9);
lean_ctor_set(x_54, 3, x_25);
lean_ctor_set(x_54, 4, x_11);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_54, 6, x_30);
x_1 = x_50;
x_2 = x_54;
x_3 = x_51;
goto _start;
}
block_73:
{
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_59; 
lean_dec(x_44);
lean_dec(x_34);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_49;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_49);
x_60 = l_Lean_Name_toString___closed__1;
x_61 = l_Lean_Name_toStringWithSep___main(x_60, x_44);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_Elab_Term_elabTermAux___main___closed__3;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Command_throwError___rarg(x_1, x_67, x_34, x_58);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_44);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
return x_46;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_46, 0);
x_151 = lean_ctor_get(x_46, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_46);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_44);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_153 = lean_ctor_get(x_45, 0);
lean_inc(x_153);
lean_dec(x_45);
x_154 = l___private_Init_Lean_Elab_Command_5__elabCommandUsing___main(x_37, x_1, x_153, x_34, x_38);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_36);
if (x_155 == 0)
{
return x_36;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_36, 0);
x_157 = lean_ctor_get(x_36, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_36);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_32);
if (x_184 == 0)
{
return x_32;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_32, 0);
x_186 = lean_ctor_get(x_32, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_32);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_188 = lean_ctor_get(x_27, 0);
x_189 = lean_ctor_get(x_27, 1);
x_190 = lean_ctor_get(x_27, 2);
x_191 = lean_ctor_get(x_27, 3);
x_192 = lean_ctor_get(x_27, 4);
x_193 = lean_ctor_get(x_27, 5);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_27);
x_194 = lean_nat_add(x_192, x_24);
x_195 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_195, 0, x_188);
lean_ctor_set(x_195, 1, x_189);
lean_ctor_set(x_195, 2, x_190);
lean_ctor_set(x_195, 3, x_191);
lean_ctor_set(x_195, 4, x_194);
lean_ctor_set(x_195, 5, x_193);
x_196 = l___private_Init_Lean_Elab_Command_3__setState(x_195, x_2, x_28);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
lean_inc(x_192);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_198 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_198, 0, x_7);
lean_ctor_set(x_198, 1, x_8);
lean_ctor_set(x_198, 2, x_9);
lean_ctor_set(x_198, 3, x_25);
lean_ctor_set(x_198, 4, x_11);
lean_ctor_set(x_198, 5, x_12);
lean_ctor_set(x_198, 6, x_192);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_309 = lean_ctor_get(x_1, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_1, 1);
lean_inc(x_310);
x_311 = l_Lean_nullKind;
x_312 = lean_name_eq(x_309, x_311);
lean_dec(x_309);
if (x_312 == 0)
{
lean_object* x_313; 
lean_dec(x_310);
lean_inc(x_198);
x_313 = l_Lean_Elab_Command_getOptions(x_198, x_197);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = l_Lean_Elab_Command_elabCommand___main___closed__1;
x_317 = l_Lean_checkTraceOption(x_314, x_316);
lean_dec(x_314);
if (x_317 == 0)
{
x_199 = x_315;
goto block_308;
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_inc(x_1);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_1);
lean_inc(x_198);
x_319 = l_Lean_Elab_Command_logTrace(x_316, x_1, x_318, x_198, x_315);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_199 = x_320;
goto block_308;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_198);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
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
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_198);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_325 = lean_ctor_get(x_313, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_313, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_327 = x_313;
} else {
 lean_dec_ref(x_313);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_329 = lean_unsigned_to_nat(0u);
x_330 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_310, x_329, x_198, x_197);
lean_dec(x_310);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_331 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_332 = l_Lean_Elab_Command_throwError___rarg(x_1, x_331, x_198, x_197);
lean_dec(x_1);
return x_332;
}
block_308:
{
lean_object* x_200; 
lean_inc(x_198);
x_200 = l___private_Init_Lean_Elab_Command_2__getState(x_198, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Elab_Command_commandElabAttribute;
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
x_206 = l_Lean_PersistentEnvExtension_getState___rarg(x_204, x_205);
lean_dec(x_205);
lean_dec(x_204);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
lean_inc(x_1);
x_208 = l_Lean_Syntax_getKind(x_1);
x_209 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_207, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
lean_dec(x_201);
lean_inc(x_198);
x_210 = l_Lean_Elab_Command_getEnv(x_198, x_202);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_221; lean_object* x_222; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
x_238 = l_Lean_Elab_Command_getCurrMacroScope(x_198, x_212);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
lean_inc(x_198);
x_241 = l_Lean_Elab_Command_getEnv(x_198, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
lean_inc(x_198);
x_244 = l___private_Init_Lean_Elab_Command_2__getState(x_198, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_environment_main_module(x_242);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_239);
lean_inc(x_1);
x_250 = l_Lean_Elab_getMacros(x_211, x_1, x_249, x_247);
lean_dec(x_211);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_198);
x_253 = l___private_Init_Lean_Elab_Command_2__getState(x_198, x_246);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_254, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_254, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_254, 4);
lean_inc(x_259);
x_260 = lean_ctor_get(x_254, 5);
lean_inc(x_260);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 lean_ctor_release(x_254, 3);
 lean_ctor_release(x_254, 4);
 lean_ctor_release(x_254, 5);
 x_261 = x_254;
} else {
 lean_dec_ref(x_254);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(0, 6, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_256);
lean_ctor_set(x_262, 1, x_252);
lean_ctor_set(x_262, 2, x_257);
lean_ctor_set(x_262, 3, x_258);
lean_ctor_set(x_262, 4, x_259);
lean_ctor_set(x_262, 5, x_260);
lean_inc(x_198);
x_263 = l___private_Init_Lean_Elab_Command_3__setState(x_262, x_198, x_255);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
lean_dec(x_213);
lean_dec(x_208);
lean_dec(x_198);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_214 = x_251;
x_215 = x_264;
goto block_220;
}
else
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_251);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
lean_dec(x_263);
x_221 = x_265;
x_222 = x_266;
goto block_237;
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_267 = lean_ctor_get(x_253, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_253, 1);
lean_inc(x_268);
lean_dec(x_253);
x_221 = x_267;
x_222 = x_268;
goto block_237;
}
}
else
{
lean_object* x_269; 
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_269 = lean_ctor_get(x_250, 0);
lean_inc(x_269);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_250, 1);
lean_inc(x_270);
lean_dec(x_250);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_198);
x_272 = l___private_Init_Lean_Elab_Command_2__getState(x_198, x_246);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 2);
lean_inc(x_276);
x_277 = lean_ctor_get(x_273, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_273, 4);
lean_inc(x_278);
x_279 = lean_ctor_get(x_273, 5);
lean_inc(x_279);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 lean_ctor_release(x_273, 3);
 lean_ctor_release(x_273, 4);
 lean_ctor_release(x_273, 5);
 x_280 = x_273;
} else {
 lean_dec_ref(x_273);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 6, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_275);
lean_ctor_set(x_281, 1, x_270);
lean_ctor_set(x_281, 2, x_276);
lean_ctor_set(x_281, 3, x_277);
lean_ctor_set(x_281, 4, x_278);
lean_ctor_set(x_281, 5, x_279);
lean_inc(x_198);
x_282 = l___private_Init_Lean_Elab_Command_3__setState(x_281, x_198, x_274);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_284, 0, x_271);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_284);
lean_inc(x_198);
x_286 = l_Lean_Elab_Command_throwError___rarg(x_1, x_285, x_198, x_283);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_221 = x_287;
x_222 = x_288;
goto block_237;
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_271);
x_289 = lean_ctor_get(x_282, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_282, 1);
lean_inc(x_290);
lean_dec(x_282);
x_221 = x_289;
x_222 = x_290;
goto block_237;
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_271);
lean_dec(x_270);
x_291 = lean_ctor_get(x_272, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_272, 1);
lean_inc(x_292);
lean_dec(x_272);
x_221 = x_291;
x_222 = x_292;
goto block_237;
}
}
else
{
lean_object* x_293; 
lean_dec(x_250);
x_293 = lean_box(1);
x_221 = x_293;
x_222 = x_246;
goto block_237;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_242);
lean_dec(x_239);
lean_dec(x_211);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_294 = lean_ctor_get(x_244, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_244, 1);
lean_inc(x_295);
lean_dec(x_244);
x_221 = x_294;
x_222 = x_295;
goto block_237;
}
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_239);
lean_dec(x_211);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_296 = lean_ctor_get(x_241, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_241, 1);
lean_inc(x_297);
lean_dec(x_241);
x_221 = x_296;
x_222 = x_297;
goto block_237;
}
block_220:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_inc(x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_1);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_12);
x_218 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_218, 0, x_7);
lean_ctor_set(x_218, 1, x_8);
lean_ctor_set(x_218, 2, x_9);
lean_ctor_set(x_218, 3, x_25);
lean_ctor_set(x_218, 4, x_11);
lean_ctor_set(x_218, 5, x_217);
lean_ctor_set(x_218, 6, x_192);
x_1 = x_214;
x_2 = x_218;
x_3 = x_215;
goto _start;
}
block_237:
{
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_223; 
lean_dec(x_208);
lean_dec(x_198);
lean_dec(x_1);
if (lean_is_scalar(x_213)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_213;
 lean_ctor_set_tag(x_223, 1);
}
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_213);
x_224 = l_Lean_Name_toString___closed__1;
x_225 = l_Lean_Name_toStringWithSep___main(x_224, x_208);
x_226 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Lean_Elab_Term_elabTermAux___main___closed__3;
x_229 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_231 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_Elab_Command_throwError___rarg(x_1, x_231, x_198, x_222);
lean_dec(x_1);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_208);
lean_dec(x_198);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_298 = lean_ctor_get(x_210, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_210, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_300 = x_210;
} else {
 lean_dec_ref(x_210);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_208);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_302 = lean_ctor_get(x_209, 0);
lean_inc(x_302);
lean_dec(x_209);
x_303 = l___private_Init_Lean_Elab_Command_5__elabCommandUsing___main(x_201, x_1, x_302, x_198, x_202);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_198);
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_304 = lean_ctor_get(x_200, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_200, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_306 = x_200;
} else {
 lean_dec_ref(x_200);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_192);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_333 = lean_ctor_get(x_196, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_196, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_335 = x_196;
} else {
 lean_dec_ref(x_196);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_2);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_337 = !lean_is_exclusive(x_26);
if (x_337 == 0)
{
return x_26;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_26, 0);
x_339 = lean_ctor_get(x_26, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_26);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_2);
x_341 = lean_unsigned_to_nat(1u);
x_342 = lean_nat_add(x_10, x_341);
lean_dec(x_10);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_342);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_343 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_343, 0, x_7);
lean_ctor_set(x_343, 1, x_8);
lean_ctor_set(x_343, 2, x_9);
lean_ctor_set(x_343, 3, x_342);
lean_ctor_set(x_343, 4, x_11);
lean_ctor_set(x_343, 5, x_12);
lean_ctor_set(x_343, 6, x_13);
lean_inc(x_343);
x_344 = l___private_Init_Lean_Elab_Command_2__getState(x_343, x_6);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_345, 2);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 3);
lean_inc(x_350);
x_351 = lean_ctor_get(x_345, 4);
lean_inc(x_351);
x_352 = lean_ctor_get(x_345, 5);
lean_inc(x_352);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_353 = x_345;
} else {
 lean_dec_ref(x_345);
 x_353 = lean_box(0);
}
x_354 = lean_nat_add(x_351, x_341);
if (lean_is_scalar(x_353)) {
 x_355 = lean_alloc_ctor(0, 6, 0);
} else {
 x_355 = x_353;
}
lean_ctor_set(x_355, 0, x_347);
lean_ctor_set(x_355, 1, x_348);
lean_ctor_set(x_355, 2, x_349);
lean_ctor_set(x_355, 3, x_350);
lean_ctor_set(x_355, 4, x_354);
lean_ctor_set(x_355, 5, x_352);
x_356 = l___private_Init_Lean_Elab_Command_3__setState(x_355, x_343, x_346);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec(x_356);
lean_inc(x_351);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_342);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_358 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_358, 0, x_7);
lean_ctor_set(x_358, 1, x_8);
lean_ctor_set(x_358, 2, x_9);
lean_ctor_set(x_358, 3, x_342);
lean_ctor_set(x_358, 4, x_11);
lean_ctor_set(x_358, 5, x_12);
lean_ctor_set(x_358, 6, x_351);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_469 = lean_ctor_get(x_1, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_1, 1);
lean_inc(x_470);
x_471 = l_Lean_nullKind;
x_472 = lean_name_eq(x_469, x_471);
lean_dec(x_469);
if (x_472 == 0)
{
lean_object* x_473; 
lean_dec(x_470);
lean_inc(x_358);
x_473 = l_Lean_Elab_Command_getOptions(x_358, x_357);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_476 = l_Lean_Elab_Command_elabCommand___main___closed__1;
x_477 = l_Lean_checkTraceOption(x_474, x_476);
lean_dec(x_474);
if (x_477 == 0)
{
x_359 = x_475;
goto block_468;
}
else
{
lean_object* x_478; lean_object* x_479; 
lean_inc(x_1);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_1);
lean_inc(x_358);
x_479 = l_Lean_Elab_Command_logTrace(x_476, x_1, x_478, x_358, x_475);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; 
x_480 = lean_ctor_get(x_479, 1);
lean_inc(x_480);
lean_dec(x_479);
x_359 = x_480;
goto block_468;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_358);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_481 = lean_ctor_get(x_479, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_479, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_483 = x_479;
} else {
 lean_dec_ref(x_479);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_358);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_485 = lean_ctor_get(x_473, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_473, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_487 = x_473;
} else {
 lean_dec_ref(x_473);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; 
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_489 = lean_unsigned_to_nat(0u);
x_490 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_470, x_489, x_358, x_357);
lean_dec(x_470);
return x_490;
}
}
else
{
lean_object* x_491; lean_object* x_492; 
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_491 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_492 = l_Lean_Elab_Command_throwError___rarg(x_1, x_491, x_358, x_357);
lean_dec(x_1);
return x_492;
}
block_468:
{
lean_object* x_360; 
lean_inc(x_358);
x_360 = l___private_Init_Lean_Elab_Command_2__getState(x_358, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = l_Lean_Elab_Command_commandElabAttribute;
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_361, 0);
lean_inc(x_365);
x_366 = l_Lean_PersistentEnvExtension_getState___rarg(x_364, x_365);
lean_dec(x_365);
lean_dec(x_364);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
lean_inc(x_1);
x_368 = l_Lean_Syntax_getKind(x_1);
x_369 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_367, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; 
lean_dec(x_361);
lean_inc(x_358);
x_370 = l_Lean_Elab_Command_getEnv(x_358, x_362);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_381; lean_object* x_382; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
x_398 = l_Lean_Elab_Command_getCurrMacroScope(x_358, x_372);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
lean_inc(x_358);
x_401 = l_Lean_Elab_Command_getEnv(x_358, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
lean_inc(x_358);
x_404 = l___private_Init_Lean_Elab_Command_2__getState(x_358, x_403);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_environment_main_module(x_402);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_399);
lean_inc(x_1);
x_410 = l_Lean_Elab_getMacros(x_371, x_1, x_409, x_407);
lean_dec(x_371);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
lean_inc(x_358);
x_413 = l___private_Init_Lean_Elab_Command_2__getState(x_358, x_406);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_414, 3);
lean_inc(x_418);
x_419 = lean_ctor_get(x_414, 4);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 5);
lean_inc(x_420);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 lean_ctor_release(x_414, 4);
 lean_ctor_release(x_414, 5);
 x_421 = x_414;
} else {
 lean_dec_ref(x_414);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(0, 6, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_416);
lean_ctor_set(x_422, 1, x_412);
lean_ctor_set(x_422, 2, x_417);
lean_ctor_set(x_422, 3, x_418);
lean_ctor_set(x_422, 4, x_419);
lean_ctor_set(x_422, 5, x_420);
lean_inc(x_358);
x_423 = l___private_Init_Lean_Elab_Command_3__setState(x_422, x_358, x_415);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; 
lean_dec(x_373);
lean_dec(x_368);
lean_dec(x_358);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_374 = x_411;
x_375 = x_424;
goto block_380;
}
else
{
lean_object* x_425; lean_object* x_426; 
lean_dec(x_411);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_dec(x_423);
x_381 = x_425;
x_382 = x_426;
goto block_397;
}
}
else
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_427 = lean_ctor_get(x_413, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_413, 1);
lean_inc(x_428);
lean_dec(x_413);
x_381 = x_427;
x_382 = x_428;
goto block_397;
}
}
else
{
lean_object* x_429; 
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_429 = lean_ctor_get(x_410, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_410, 1);
lean_inc(x_430);
lean_dec(x_410);
x_431 = lean_ctor_get(x_429, 0);
lean_inc(x_431);
lean_dec(x_429);
lean_inc(x_358);
x_432 = l___private_Init_Lean_Elab_Command_2__getState(x_358, x_406);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_433, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_433, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_433, 4);
lean_inc(x_438);
x_439 = lean_ctor_get(x_433, 5);
lean_inc(x_439);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 lean_ctor_release(x_433, 4);
 lean_ctor_release(x_433, 5);
 x_440 = x_433;
} else {
 lean_dec_ref(x_433);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(0, 6, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_435);
lean_ctor_set(x_441, 1, x_430);
lean_ctor_set(x_441, 2, x_436);
lean_ctor_set(x_441, 3, x_437);
lean_ctor_set(x_441, 4, x_438);
lean_ctor_set(x_441, 5, x_439);
lean_inc(x_358);
x_442 = l___private_Init_Lean_Elab_Command_3__setState(x_441, x_358, x_434);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
lean_dec(x_442);
x_444 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_444, 0, x_431);
x_445 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_445, 0, x_444);
lean_inc(x_358);
x_446 = l_Lean_Elab_Command_throwError___rarg(x_1, x_445, x_358, x_443);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
x_381 = x_447;
x_382 = x_448;
goto block_397;
}
else
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_431);
x_449 = lean_ctor_get(x_442, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_442, 1);
lean_inc(x_450);
lean_dec(x_442);
x_381 = x_449;
x_382 = x_450;
goto block_397;
}
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_431);
lean_dec(x_430);
x_451 = lean_ctor_get(x_432, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_432, 1);
lean_inc(x_452);
lean_dec(x_432);
x_381 = x_451;
x_382 = x_452;
goto block_397;
}
}
else
{
lean_object* x_453; 
lean_dec(x_410);
x_453 = lean_box(1);
x_381 = x_453;
x_382 = x_406;
goto block_397;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; 
lean_dec(x_402);
lean_dec(x_399);
lean_dec(x_371);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_454 = lean_ctor_get(x_404, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_404, 1);
lean_inc(x_455);
lean_dec(x_404);
x_381 = x_454;
x_382 = x_455;
goto block_397;
}
}
else
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_399);
lean_dec(x_371);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_456 = lean_ctor_get(x_401, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_401, 1);
lean_inc(x_457);
lean_dec(x_401);
x_381 = x_456;
x_382 = x_457;
goto block_397;
}
block_380:
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_inc(x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_1);
lean_ctor_set(x_376, 1, x_374);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_12);
x_378 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_378, 0, x_7);
lean_ctor_set(x_378, 1, x_8);
lean_ctor_set(x_378, 2, x_9);
lean_ctor_set(x_378, 3, x_342);
lean_ctor_set(x_378, 4, x_11);
lean_ctor_set(x_378, 5, x_377);
lean_ctor_set(x_378, 6, x_351);
x_1 = x_374;
x_2 = x_378;
x_3 = x_375;
goto _start;
}
block_397:
{
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_383; 
lean_dec(x_368);
lean_dec(x_358);
lean_dec(x_1);
if (lean_is_scalar(x_373)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_373;
 lean_ctor_set_tag(x_383, 1);
}
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_373);
x_384 = l_Lean_Name_toString___closed__1;
x_385 = l_Lean_Name_toStringWithSep___main(x_384, x_368);
x_386 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_386, 0, x_385);
x_387 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_387, 0, x_386);
x_388 = l_Lean_Elab_Term_elabTermAux___main___closed__3;
x_389 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_387);
x_390 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_391 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_392 = l_Lean_Elab_Command_throwError___rarg(x_1, x_391, x_358, x_382);
lean_dec(x_1);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_395 = x_392;
} else {
 lean_dec_ref(x_392);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_368);
lean_dec(x_358);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_458 = lean_ctor_get(x_370, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_370, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_460 = x_370;
} else {
 lean_dec_ref(x_370);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
else
{
lean_object* x_462; lean_object* x_463; 
lean_dec(x_368);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_462 = lean_ctor_get(x_369, 0);
lean_inc(x_462);
lean_dec(x_369);
x_463 = l___private_Init_Lean_Elab_Command_5__elabCommandUsing___main(x_361, x_1, x_462, x_358, x_362);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_358);
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_464 = lean_ctor_get(x_360, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_360, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_466 = x_360;
} else {
 lean_dec_ref(x_360);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_465);
return x_467;
}
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_351);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_493 = lean_ctor_get(x_356, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_356, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_495 = x_356;
} else {
 lean_dec_ref(x_356);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_497 = lean_ctor_get(x_344, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_344, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_499 = x_344;
} else {
 lean_dec_ref(x_344);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; uint8_t x_503; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_501 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_502 = l_Lean_Elab_Command_throwError___rarg(x_1, x_501, x_2, x_6);
lean_dec(x_1);
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
return x_502;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_502, 0);
x_505 = lean_ctor_get(x_502, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_502);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
else
{
uint8_t x_507; 
lean_dec(x_2);
lean_dec(x_1);
x_507 = !lean_is_exclusive(x_4);
if (x_507 == 0)
{
return x_4;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_4, 0);
x_509 = lean_ctor_get(x_4, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_4);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___main___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___main___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCommand___main___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabCommand___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_3, 5, x_11);
x_12 = l_Lean_Elab_Command_elabCommand___main(x_6, x_3, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 6);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_19);
x_23 = l_Lean_Elab_Command_elabCommand___main(x_6, x_22, x_7);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__mkTermContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = 1;
x_8 = 0;
x_9 = 1;
x_10 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 2, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 3, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 6, x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
x_16 = lean_ctor_get(x_1, 6);
x_17 = lean_ctor_get(x_2, 5);
x_18 = l_Lean_LocalContext_Inhabited___closed__2;
x_19 = l_Array_empty___closed__1;
lean_inc(x_17);
lean_inc(x_13);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_13);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_ctor_get(x_5, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 4);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
x_24 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_14);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_3);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_7);
lean_ctor_set_uint8(x_24, sizeof(void*)*10 + 1, x_7);
return x_24;
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__mkTermContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Command_7__mkTermState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 4);
x_6 = l_Lean_MetavarContext_Inhabited___closed__1;
x_7 = l_Lean_Meta_MetaHasEval___rarg___closed__4;
x_8 = l_Lean_TraceState_Inhabited___closed__1;
x_9 = l_PersistentArray_empty___closed__3;
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_3);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_9);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_4);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_5);
return x_13;
}
}
lean_object* l___private_Init_Lean_Elab_Command_7__mkTermState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_8__updateState(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 5);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_ctor_get(x_1, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_ctor_set(x_1, 4, x_6);
lean_ctor_set(x_1, 2, x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 3);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_17);
lean_inc(x_16);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_19);
return x_20;
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_8__updateState___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_8__updateState(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_9__getVarDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_2);
x_4 = lean_ctor_get(x_3, 6);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Command_9__getVarDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_Exception_inhabited;
x_2 = l_Lean_Elab_Command_State_inhabited;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Init_Lean_Elab_Command_8__updateState(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l___private_Init_Lean_Elab_Command_8__updateState(x_1, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l___private_Init_Lean_Elab_Command_8__updateState(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l___private_Init_Lean_Elab_Command_8__updateState(x_1, x_16);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg___closed__1;
x_21 = l_unreachable_x21___rarg(x_20);
return x_21;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_10__toCommandResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_10__toCommandResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_10__toCommandResult(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Exception_inhabited___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed), 3, 1);
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
lean_object* _init_l_Lean_Elab_Command_runTermElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_inhabited(lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_6);
x_9 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_3, x_6, x_1);
x_10 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_6);
lean_dec(x_6);
x_11 = l_Lean_Elab_Term_elabBinders___rarg(x_8, x_2, x_9, x_10);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
lean_ctor_set(x_16, 2, x_18);
lean_ctor_set(x_16, 0, x_19);
x_23 = l___private_Init_Lean_Elab_Command_3__setState(x_16, x_3, x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_12);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
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
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 3);
x_34 = lean_ctor_get(x_16, 4);
x_35 = lean_ctor_get(x_16, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_34);
lean_ctor_set(x_36, 5, x_35);
x_37 = l___private_Init_Lean_Elab_Command_3__setState(x_36, x_3, x_17);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
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
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_dec(x_11);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_3);
x_52 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_50, 2);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
lean_ctor_set(x_54, 2, x_56);
lean_ctor_set(x_54, 0, x_57);
x_61 = l___private_Init_Lean_Elab_Command_3__setState(x_54, x_3, x_55);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_51);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_51);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_54, 1);
x_71 = lean_ctor_get(x_54, 3);
x_72 = lean_ctor_get(x_54, 4);
x_73 = lean_ctor_get(x_54, 5);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_74 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_74, 0, x_57);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_56);
lean_ctor_set(x_74, 3, x_71);
lean_ctor_set(x_74, 4, x_72);
lean_ctor_set(x_74, 5, x_73);
x_75 = l___private_Init_Lean_Elab_Command_3__setState(x_74, x_3, x_55);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_51);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_51);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_52);
if (x_83 == 0)
{
return x_52;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_52, 0);
x_85 = lean_ctor_get(x_52, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_52);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_11);
x_87 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_88 = l_unreachable_x21___rarg(x_87);
x_89 = lean_apply_2(x_88, x_3, x_7);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
return x_5;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_5, 0);
x_92 = lean_ctor_get(x_5, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_5);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withLogging(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = l_PersistentArray_push___rarg(x_12, x_7);
lean_ctor_set(x_9, 2, x_13);
x_14 = l___private_Init_Lean_Elab_Command_3__setState(x_9, x_2, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
x_27 = lean_ctor_get(x_9, 2);
x_28 = lean_ctor_get(x_9, 3);
x_29 = lean_ctor_get(x_9, 4);
x_30 = lean_ctor_get(x_9, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_31 = l_PersistentArray_push___rarg(x_27, x_7);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
x_33 = l___private_Init_Lean_Elab_Command_3__setState(x_32, x_2, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_dec(x_4);
x_47 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_48 = l_unreachable_x21___rarg(x_47);
x_49 = lean_apply_2(x_48, x_2, x_46);
return x_49;
}
}
}
}
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 2);
x_17 = l_PersistentArray_push___rarg(x_16, x_11);
lean_ctor_set(x_13, 2, x_17);
x_18 = l___private_Init_Lean_Elab_Command_3__setState(x_13, x_2, x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set_tag(x_18, 0);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
x_34 = lean_ctor_get(x_13, 3);
x_35 = lean_ctor_get(x_13, 4);
x_36 = lean_ctor_get(x_13, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_37 = l_PersistentArray_push___rarg(x_33, x_11);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_36);
x_39 = l___private_Init_Lean_Elab_Command_3__setState(x_38, x_2, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_12, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_50);
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_dec(x_12);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_dec(x_4);
x_55 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_56 = l_unreachable_x21___rarg(x_55);
x_57 = lean_apply_2(x_56, x_2, x_54);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
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
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set_tag(x_57, 0);
lean_ctor_set(x_57, 0, x_64);
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_dbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_7 = lean_dbg_trace(x_5, x_6);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_dbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_dbgTrace___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_setEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_1);
x_9 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_6);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
x_24 = lean_ctor_get(x_5, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
x_26 = l___private_Init_Lean_Elab_Command_3__setState(x_25, x_2, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
return x_4;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_Elab_Command_getCurrNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 3);
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
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_11__addScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l___private_Init_Lean_Elab_Command_2__getState(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 3);
lean_inc(x_3);
x_12 = l_Lean_Environment_registerNamespace___main(x_10, x_3);
x_13 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 3, x_3);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 0, x_1);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_7, 3, x_18);
lean_ctor_set(x_7, 0, x_12);
x_19 = l___private_Init_Lean_Elab_Command_3__setState(x_7, x_4, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
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
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_13, 2);
x_31 = lean_ctor_get(x_13, 4);
x_32 = lean_ctor_get(x_13, 5);
x_33 = lean_ctor_get(x_13, 6);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_34 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_3);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
lean_ctor_set(x_34, 6, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
lean_ctor_set(x_7, 3, x_35);
lean_ctor_set(x_7, 0, x_12);
x_36 = l___private_Init_Lean_Elab_Command_3__setState(x_7, x_4, x_8);
if (lean_obj_tag(x_36) == 0)
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
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
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
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
x_47 = lean_ctor_get(x_7, 2);
x_48 = lean_ctor_get(x_7, 3);
x_49 = lean_ctor_get(x_7, 4);
x_50 = lean_ctor_get(x_7, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
lean_inc(x_3);
x_51 = l_Lean_Environment_registerNamespace___main(x_45, x_3);
x_52 = l_List_head_x21___at_Lean_Elab_Command_getScope___spec__1(x_48);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 6);
lean_inc(x_56);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 lean_ctor_release(x_52, 6);
 x_57 = x_52;
} else {
 lean_dec_ref(x_52);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 7, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_3);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
lean_ctor_set(x_58, 6, x_56);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_48);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_49);
lean_ctor_set(x_60, 5, x_50);
x_61 = l___private_Init_Lean_Elab_Command_3__setState(x_60, x_4, x_8);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_6);
if (x_70 == 0)
{
return x_6;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_6, 0);
x_72 = lean_ctor_get(x_6, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_6);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid scope");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_2, x_3, x_9, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_5);
x_13 = l_Lean_Elab_Command_getCurrNamespace(x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
if (x_3 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Init_Lean_Elab_Command_11__addScope(x_2, x_10, x_14, x_5, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
lean_inc(x_10);
x_20 = lean_name_mk_string(x_19, x_10);
x_21 = l_Lean_Name_append___main(x_17, x_20);
lean_dec(x_17);
x_22 = l___private_Init_Lean_Elab_Command_11__addScope(x_2, x_10, x_21, x_5, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_5);
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
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
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
default: 
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_2);
x_31 = l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__3;
x_32 = l_Lean_Elab_Command_throwError___rarg(x_1, x_31, x_5, x_6);
return x_32;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Elab_Command_12__addScopes(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Command_13__addNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_6 = 1;
x_7 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Command_13__addNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Command_13__addNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Command_namespace___elambda__1___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Init_Lean_Elab_Term_4__isCDot___closed__1;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
x_12 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_13 = 1;
x_14 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_12, x_13, x_11, x_2, x_3);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = l_Lean_Syntax_getArgs(x_1);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_25 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_26 = 1;
x_27 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_25, x_26, x_24, x_2, x_3);
lean_dec(x_1);
return x_27;
}
}
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNamespace");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNamespace), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_namespace___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_inc(x_1);
x_62 = l_Lean_Syntax_isOfKind(x_1, x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 0;
x_4 = x_63;
goto block_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = l_Lean_Syntax_getArgs(x_1);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
x_4 = x_67;
goto block_60;
}
block_60:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_nullKind___closed__2;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_56; 
x_56 = 0;
x_12 = x_56;
goto block_55;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_Syntax_getArgs(x_9);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_59 = lean_nat_dec_eq(x_58, x_8);
lean_dec(x_58);
x_12 = x_59;
goto block_55;
}
block_55:
{
uint8_t x_13; 
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_dec(x_1);
if (x_11 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
x_14 = l___private_Init_Lean_Elab_Term_4__isCDot___closed__1;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; 
lean_inc(x_2);
x_17 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_21 = l_String_splitAux___main___closed__1;
x_22 = l___private_Init_Lean_Elab_Command_11__addScope(x_20, x_21, x_18, x_2, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_27 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
else
{
lean_object* x_34; 
lean_inc(x_2);
x_34 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_3);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_38 = l_String_splitAux___main___closed__1;
x_39 = l___private_Init_Lean_Elab_Command_11__addScope(x_37, x_38, x_35, x_2, x_36);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_Syntax_getArg(x_9, x_44);
lean_dec(x_9);
x_46 = l_Lean_Syntax_getKind___closed__4;
lean_inc(x_45);
x_47 = l_Lean_Syntax_isOfKind(x_45, x_46);
x_48 = l_coeDecidableEq(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(1);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_3);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_51 = l_Lean_Syntax_getId(x_45);
lean_dec(x_45);
x_52 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_53 = 0;
x_54 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_52, x_53, x_51, x_2, x_3);
lean_dec(x_1);
return x_54;
}
}
}
}
}
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSection");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSection), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_section___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getScopes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_2__getState(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 3);
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
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
uint8_t l___private_Init_Lean_Elab_Command_14__checkAnonymousScope(lean_object* x_1) {
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
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_14__checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Command_14__checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Elab_Command_15__checkEndHeader___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Lean_Elab_Command_15__checkEndHeader___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_Command_15__checkEndHeader___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Elab_Command_15__checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Elab_Command_15__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_15__checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_Command_15__checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name is missing");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name mismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', insufficient scopes");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_103; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getOptionalIdent_x3f(x_5);
lean_dec(x_5);
lean_inc(x_2);
x_103 = l_Lean_Elab_Command_getScopes(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_7 = x_4;
x_8 = x_104;
x_9 = x_105;
goto block_102;
}
else
{
uint8_t x_106; 
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_6, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
lean_dec(x_103);
x_113 = l_Lean_Name_getNumParts___main(x_110);
lean_dec(x_110);
x_7 = x_113;
x_8 = x_111;
x_9 = x_112;
goto block_102;
}
else
{
uint8_t x_114; 
lean_dec(x_6);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_103);
if (x_114 == 0)
{
return x_103;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_103, 0);
x_116 = lean_ctor_get(x_103, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_103);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
block_102:
{
lean_object* x_10; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_List_lengthAux___main___rarg(x_8, x_23);
x_25 = lean_nat_dec_lt(x_7, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_2);
x_26 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 3);
x_31 = l_List_lengthAux___main___rarg(x_30, x_23);
x_32 = lean_nat_sub(x_31, x_4);
lean_dec(x_31);
x_33 = l_List_drop___main___rarg(x_32, x_30);
lean_dec(x_30);
lean_ctor_set(x_27, 3, x_33);
lean_inc(x_2);
x_34 = l___private_Init_Lean_Elab_Command_3__setState(x_27, x_2, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Command_elabEnd___closed__9;
x_37 = l_Lean_Elab_Command_throwError___rarg(x_1, x_36, x_2, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
x_48 = lean_ctor_get(x_27, 2);
x_49 = lean_ctor_get(x_27, 3);
x_50 = lean_ctor_get(x_27, 4);
x_51 = lean_ctor_get(x_27, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_52 = l_List_lengthAux___main___rarg(x_49, x_23);
x_53 = lean_nat_sub(x_52, x_4);
lean_dec(x_52);
x_54 = l_List_drop___main___rarg(x_53, x_49);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_48);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_50);
lean_ctor_set(x_55, 5, x_51);
lean_inc(x_2);
x_56 = l___private_Init_Lean_Elab_Command_3__setState(x_55, x_2, x_28);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Elab_Command_elabEnd___closed__9;
x_59 = l_Lean_Elab_Command_throwError___rarg(x_1, x_58, x_2, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_66 = x_56;
} else {
 lean_dec_ref(x_56);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
return x_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_26, 0);
x_70 = lean_ctor_get(x_26, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_26);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; 
lean_inc(x_2);
x_72 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 3);
x_77 = l_List_drop___main___rarg(x_7, x_76);
lean_dec(x_76);
lean_ctor_set(x_73, 3, x_77);
lean_inc(x_2);
x_78 = l___private_Init_Lean_Elab_Command_3__setState(x_73, x_2, x_74);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_10 = x_79;
goto block_22;
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_78);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_73, 0);
x_85 = lean_ctor_get(x_73, 1);
x_86 = lean_ctor_get(x_73, 2);
x_87 = lean_ctor_get(x_73, 3);
x_88 = lean_ctor_get(x_73, 4);
x_89 = lean_ctor_get(x_73, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_73);
x_90 = l_List_drop___main___rarg(x_7, x_87);
lean_dec(x_87);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_85);
lean_ctor_set(x_91, 2, x_86);
lean_ctor_set(x_91, 3, x_90);
lean_ctor_set(x_91, 4, x_88);
lean_ctor_set(x_91, 5, x_89);
lean_inc(x_2);
x_92 = l___private_Init_Lean_Elab_Command_3__setState(x_91, x_2, x_74);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_10 = x_93;
goto block_22;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
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
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_72);
if (x_98 == 0)
{
return x_72;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_72, 0);
x_100 = lean_ctor_get(x_72, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_72);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_22:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = l___private_Init_Lean_Elab_Command_14__checkAnonymousScope(x_8);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_Command_elabEnd___closed__3;
x_13 = l_Lean_Elab_Command_throwError___rarg(x_1, x_12, x_2, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l___private_Init_Lean_Elab_Command_15__checkEndHeader___main(x_16, x_8);
lean_dec(x_8);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Elab_Command_elabEnd___closed__6;
x_19 = l_Lean_Elab_Command_throwError___rarg(x_1, x_18, x_2, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabEnd(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabEnd");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_end___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_7 = 1;
lean_inc(x_4);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_6, x_7, x_2, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_4);
x_10 = lean_apply_2(x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
x_13 = l___private_Init_Lean_Elab_Command_2__getState(x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 3);
x_18 = l_Lean_Name_getNumParts___main(x_2);
lean_dec(x_2);
x_19 = l_List_drop___main___rarg(x_18, x_17);
lean_dec(x_17);
lean_ctor_set(x_14, 3, x_19);
x_20 = l___private_Init_Lean_Elab_Command_3__setState(x_14, x_4, x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
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
uint8_t x_25; 
lean_dec(x_11);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
x_31 = lean_ctor_get(x_14, 2);
x_32 = lean_ctor_get(x_14, 3);
x_33 = lean_ctor_get(x_14, 4);
x_34 = lean_ctor_get(x_14, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_35 = l_Lean_Name_getNumParts___main(x_2);
lean_dec(x_2);
x_36 = l_List_drop___main___rarg(x_35, x_32);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
x_38 = l___private_Init_Lean_Elab_Command_3__setState(x_37, x_4, x_15);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
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
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
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
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
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
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_Elab_Command_withNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withNamespace___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withNamespace___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_withNamespace___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad;
x_2 = l_Lean_Elab_Command_Scope_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_modifyScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 3);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_apply_1(x_1, x_44);
lean_ctor_set(x_6, 0, x_45);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
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
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_6, 0);
x_58 = lean_ctor_get(x_6, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_6);
x_59 = lean_apply_1(x_1, x_57);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_5, 3, x_60);
x_61 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_70 = lean_ctor_get(x_5, 0);
x_71 = lean_ctor_get(x_5, 1);
x_72 = lean_ctor_get(x_5, 2);
x_73 = lean_ctor_get(x_5, 4);
x_74 = lean_ctor_get(x_5, 5);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_5);
x_75 = lean_ctor_get(x_6, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_6, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_77 = x_6;
} else {
 lean_dec_ref(x_6);
 x_77 = lean_box(0);
}
x_78 = lean_apply_1(x_1, x_75);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
x_80 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_72);
lean_ctor_set(x_80, 3, x_79);
lean_ctor_set(x_80, 4, x_73);
lean_ctor_set(x_80, 5, x_74);
x_81 = l___private_Init_Lean_Elab_Command_3__setState(x_80, x_2, x_40);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
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
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
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
}
}
else
{
uint8_t x_90; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_4);
if (x_90 == 0)
{
return x_4;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_4, 0);
x_92 = lean_ctor_get(x_4, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_4);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
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
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a universe level named '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerAttributeImplBuilder___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_2);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Command_throwError___rarg(x_1, x_12, x_3, x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_6, 1);
x_46 = lean_ctor_get(x_6, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 5);
lean_ctor_set(x_6, 1, x_48);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_40, 5, x_6);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_5, 3, x_49);
x_50 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_40, 0);
x_62 = lean_ctor_get(x_40, 1);
x_63 = lean_ctor_get(x_40, 2);
x_64 = lean_ctor_get(x_40, 3);
x_65 = lean_ctor_get(x_40, 4);
x_66 = lean_ctor_get(x_40, 5);
x_67 = lean_ctor_get(x_40, 6);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_40);
lean_ctor_set(x_6, 1, x_66);
lean_ctor_set(x_6, 0, x_1);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_6);
lean_ctor_set(x_68, 6, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_45);
lean_ctor_set(x_5, 3, x_69);
x_70 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_dec(x_6);
x_80 = lean_ctor_get(x_40, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_40, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_40, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_40, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_40, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_40, 6);
lean_inc(x_86);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_87 = x_40;
} else {
 lean_dec_ref(x_40);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 7, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_82);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_84);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set(x_89, 6, x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_79);
lean_ctor_set(x_5, 3, x_90);
x_91 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_100 = lean_ctor_get(x_5, 0);
x_101 = lean_ctor_get(x_5, 1);
x_102 = lean_ctor_get(x_5, 2);
x_103 = lean_ctor_get(x_5, 4);
x_104 = lean_ctor_get(x_5, 5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_5);
x_105 = lean_ctor_get(x_6, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_106 = x_6;
} else {
 lean_dec_ref(x_6);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_40, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_40, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_40, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_40, 6);
lean_inc(x_113);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_114 = x_40;
} else {
 lean_dec_ref(x_40);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_106;
}
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_112);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 7, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_108);
lean_ctor_set(x_116, 2, x_109);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set(x_116, 4, x_111);
lean_ctor_set(x_116, 5, x_115);
lean_ctor_set(x_116, 6, x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_105);
x_118 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_118, 0, x_100);
lean_ctor_set(x_118, 1, x_101);
lean_ctor_set(x_118, 2, x_102);
lean_ctor_set(x_118, 3, x_117);
lean_ctor_set(x_118, 4, x_103);
lean_ctor_set(x_118, 5, x_104);
x_119 = l___private_Init_Lean_Elab_Command_3__setState(x_118, x_2, x_41);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_126 = x_119;
} else {
 lean_dec_ref(x_119);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_4);
if (x_128 == 0)
{
return x_4;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_4, 0);
x_130 = lean_ctor_get(x_4, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_4);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Syntax_getId(x_1);
lean_inc(x_2);
x_5 = l_Lean_Elab_Command_getLevelNames(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(x_4, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_4, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_1, x_4, x_2, x_7);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_addUnivLevel(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Elab_Command_addUnivLevel(x_5, x_2, x_3);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabUniverse(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabUniverse");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverse___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_universe___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_5);
x_13 = l_Lean_Elab_Command_addUnivLevel(x_10, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_3 = x_12;
x_4 = x_14;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(0);
x_9 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_6, x_7, x_8, x_2, x_3);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabUniverses(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabUniverses");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverses___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(4);
x_8 = lean_add_decl(x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_Elab_Command_getOptions(x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_KernelException_toMessageData(x_9, x_11);
x_14 = l_Lean_Elab_Command_throwError___rarg(x_1, x_13, x_2, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_2);
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
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lean_Elab_Command_setEnv(x_19, x_2, x_6);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabInitQuot(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabInitQuot");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_init__quot___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getOpenDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 4);
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
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_logUnknownDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addClass___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_logUnknownDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_logUnknownDecl___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_2);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_Command_logUnknownDecl___closed__2;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Term_mkConst___closed__4;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 2;
x_14 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_13, x_12, x_3, x_4);
return x_14;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_logUnknownDecl(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getOpenDecls(x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_resolveNamespace(x_5, x_8, x_12, x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_box(1);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = l_Lean_Elab_resolveNamespace(x_5, x_8, x_16, x_1);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
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
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
return x_4;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = l_Lean_Syntax_getId(x_13);
lean_inc(x_16);
x_17 = l_Lean_Name_append___main(x_2, x_16);
lean_inc(x_4);
x_18 = l_Lean_Environment_contains(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_inc(x_8);
x_19 = l_Lean_Elab_Command_logUnknownDecl(x_13, x_17, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_6 = x_15;
x_9 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
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
lean_dec(x_13);
x_26 = l_Lean_Name_append___main(x_3, x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
x_6 = x_15;
x_7 = x_28;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'export', self export");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabExport(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getIdAt(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_resolveNamespace(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_71; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_71 = lean_name_eq(x_7, x_10);
if (x_71 == 0)
{
x_12 = x_11;
goto block_70;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_10);
lean_dec(x_7);
x_72 = l_Lean_Elab_Command_elabExport___closed__3;
x_73 = l_Lean_Elab_Command_throwError___rarg(x_1, x_72, x_2, x_11);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
block_70:
{
lean_object* x_13; 
lean_inc(x_2);
x_13 = l_Lean_Elab_Command_getEnv(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_21 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_7, x_10, x_14, x_18, x_20, x_19, x_2, x_15);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_2);
x_24 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_28, x_22);
lean_ctor_set(x_25, 0, x_29);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_25, x_2, x_26);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 2);
x_44 = lean_ctor_get(x_25, 3);
x_45 = lean_ctor_get(x_25, 4);
x_46 = lean_ctor_get(x_25, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_47 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_41, x_22);
x_48 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_44);
lean_ctor_set(x_48, 4, x_45);
lean_ctor_set(x_48, 5, x_46);
x_49 = l___private_Init_Lean_Elab_Command_3__setState(x_48, x_2, x_26);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_56 = x_49;
} else {
 lean_dec_ref(x_49);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_22);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_24);
if (x_58 == 0)
{
return x_24;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
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
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_21);
if (x_62 == 0)
{
return x_21;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_21, 0);
x_64 = lean_ctor_get(x_21, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_13);
if (x_66 == 0)
{
return x_13;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_13, 0);
x_68 = lean_ctor_get(x_13, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_13);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_7);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_9);
if (x_78 == 0)
{
return x_9;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_9, 0);
x_80 = lean_ctor_get(x_9, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_9);
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
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_6);
if (x_82 == 0)
{
return x_6;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_6, 0);
x_84 = lean_ctor_get(x_6, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_6);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabExport(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabExport");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabExport___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_export___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_6, 1);
x_46 = lean_ctor_get(x_6, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 4);
lean_ctor_set(x_6, 1, x_48);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_40, 4, x_6);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_5, 3, x_49);
x_50 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_40, 0);
x_62 = lean_ctor_get(x_40, 1);
x_63 = lean_ctor_get(x_40, 2);
x_64 = lean_ctor_get(x_40, 3);
x_65 = lean_ctor_get(x_40, 4);
x_66 = lean_ctor_get(x_40, 5);
x_67 = lean_ctor_get(x_40, 6);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_40);
lean_ctor_set(x_6, 1, x_65);
lean_ctor_set(x_6, 0, x_1);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_6);
lean_ctor_set(x_68, 5, x_66);
lean_ctor_set(x_68, 6, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_45);
lean_ctor_set(x_5, 3, x_69);
x_70 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_dec(x_6);
x_80 = lean_ctor_get(x_40, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_40, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_40, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_40, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_40, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_40, 6);
lean_inc(x_86);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_87 = x_40;
} else {
 lean_dec_ref(x_40);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_84);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 7, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_82);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_85);
lean_ctor_set(x_89, 6, x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_79);
lean_ctor_set(x_5, 3, x_90);
x_91 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_100 = lean_ctor_get(x_5, 0);
x_101 = lean_ctor_get(x_5, 1);
x_102 = lean_ctor_get(x_5, 2);
x_103 = lean_ctor_get(x_5, 4);
x_104 = lean_ctor_get(x_5, 5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_5);
x_105 = lean_ctor_get(x_6, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_106 = x_6;
} else {
 lean_dec_ref(x_6);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_40, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_40, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_40, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_40, 6);
lean_inc(x_113);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_114 = x_40;
} else {
 lean_dec_ref(x_40);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_106;
}
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_111);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 7, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_108);
lean_ctor_set(x_116, 2, x_109);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set(x_116, 4, x_115);
lean_ctor_set(x_116, 5, x_112);
lean_ctor_set(x_116, 6, x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_105);
x_118 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_118, 0, x_100);
lean_ctor_set(x_118, 1, x_101);
lean_ctor_set(x_118, 2, x_102);
lean_ctor_set(x_118, 3, x_117);
lean_ctor_set(x_118, 4, x_103);
lean_ctor_set(x_118, 5, x_104);
x_119 = l___private_Init_Lean_Elab_Command_3__setState(x_118, x_2, x_41);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_126 = x_119;
} else {
 lean_dec_ref(x_119);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_4);
if (x_128 == 0)
{
return x_4;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_4, 0);
x_130 = lean_ctor_get(x_4, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_4);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
lean_inc(x_5);
x_14 = l_Lean_Elab_Command_resolveNamespace(x_13, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_5);
x_19 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_18, x_5, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_3 = x_12;
x_4 = x_20;
x_6 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_5);
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
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_4, x_8, x_6, x_9, x_2, x_3);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenSimple(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = l_Lean_Syntax_getId(x_11);
lean_inc(x_14);
x_15 = l_Lean_Name_append___main(x_2, x_14);
lean_inc(x_6);
x_16 = l_Lean_Elab_Command_getEnv(x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Environment_contains(x_17, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_6);
x_20 = l_Lean_Elab_Command_logUnknownDecl(x_11, x_15, x_6, x_18);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_13;
x_5 = x_21;
x_7 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
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
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_inc(x_6);
x_29 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_28, x_6, x_18);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_4 = x_13;
x_5 = x_30;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_6);
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
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_4, x_10, x_14, x_6, x_15, x_2, x_11);
lean_dec(x_14);
lean_dec(x_10);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenOnly(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = l_Lean_Syntax_getId(x_12);
lean_inc(x_15);
x_16 = l_Lean_Name_append___main(x_2, x_15);
lean_inc(x_3);
x_17 = l_Lean_Environment_contains(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_inc(x_7);
x_18 = l_Lean_Elab_Command_logUnknownDecl(x_12, x_16, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_5 = x_14;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_6);
x_5 = x_14;
x_6 = x_25;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l_Lean_Elab_Command_getEnv(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_array_get(x_5, x_4, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
lean_inc(x_2);
x_19 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_4, x_10, x_13, x_18, x_6, x_17, x_2, x_14);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_22, x_2, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_2);
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
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
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
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenHiding(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getIdAt(x_11, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getIdAt(x_11, x_14);
x_16 = l_Lean_Name_append___main(x_1, x_13);
lean_inc(x_6);
x_17 = l_Lean_Elab_Command_getEnv(x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Environment_contains(x_18, x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
lean_inc(x_6);
x_21 = l_Lean_Elab_Command_logUnknownDecl(x_11, x_16, x_6, x_19);
lean_dec(x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_24;
x_5 = x_22;
x_7 = x_23;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_4);
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
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_inc(x_6);
x_31 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_30, x_6, x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_34;
x_5 = x_32;
x_7 = x_33;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
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
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_10, x_12, x_14, x_6, x_15, x_2, x_11);
lean_dec(x_14);
lean_dec(x_10);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpenRenaming(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_asNode(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
x_9 = lean_name_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_11 = lean_name_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_13 = lean_name_eq(x_7, x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Command_elabOpenRenaming(x_6, x_2, x_3);
lean_dec(x_6);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabOpenHiding(x_6, x_2, x_3);
lean_dec(x_6);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
x_16 = l_Lean_Elab_Command_elabOpenOnly(x_6, x_2, x_3);
lean_dec(x_6);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = l_Lean_Elab_Command_elabOpenSimple(x_6, x_2, x_3);
lean_dec(x_6);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabOpen(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabOpen");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabOpen___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 6);
x_48 = lean_array_push(x_47, x_1);
lean_ctor_set(x_40, 6, x_48);
x_49 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
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
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
x_62 = lean_ctor_get(x_40, 2);
x_63 = lean_ctor_get(x_40, 3);
x_64 = lean_ctor_get(x_40, 4);
x_65 = lean_ctor_get(x_40, 5);
x_66 = lean_ctor_get(x_40, 6);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_67 = lean_array_push(x_66, x_1);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_62);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_67);
lean_ctor_set(x_6, 0, x_68);
x_69 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_6, 1);
lean_inc(x_78);
lean_dec(x_6);
x_79 = lean_ctor_get(x_40, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_40, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_40, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_40, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_40, 6);
lean_inc(x_85);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_86 = x_40;
} else {
 lean_dec_ref(x_40);
 x_86 = lean_box(0);
}
x_87 = lean_array_push(x_85, x_1);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 7, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_81);
lean_ctor_set(x_88, 3, x_82);
lean_ctor_set(x_88, 4, x_83);
lean_ctor_set(x_88, 5, x_84);
lean_ctor_set(x_88, 6, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
lean_ctor_set(x_5, 3, x_89);
x_90 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
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
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_99 = lean_ctor_get(x_5, 0);
x_100 = lean_ctor_get(x_5, 1);
x_101 = lean_ctor_get(x_5, 2);
x_102 = lean_ctor_get(x_5, 4);
x_103 = lean_ctor_get(x_5, 5);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_5);
x_104 = lean_ctor_get(x_6, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_105 = x_6;
} else {
 lean_dec_ref(x_6);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_40, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_40, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_40, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 5);
lean_inc(x_111);
x_112 = lean_ctor_get(x_40, 6);
lean_inc(x_112);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_113 = x_40;
} else {
 lean_dec_ref(x_40);
 x_113 = lean_box(0);
}
x_114 = lean_array_push(x_112, x_1);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 7, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_106);
lean_ctor_set(x_115, 1, x_107);
lean_ctor_set(x_115, 2, x_108);
lean_ctor_set(x_115, 3, x_109);
lean_ctor_set(x_115, 4, x_110);
lean_ctor_set(x_115, 5, x_111);
lean_ctor_set(x_115, 6, x_114);
if (lean_is_scalar(x_105)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_105;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_104);
x_117 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_117, 0, x_99);
lean_ctor_set(x_117, 1, x_100);
lean_ctor_set(x_117, 2, x_101);
lean_ctor_set(x_117, 3, x_116);
lean_ctor_set(x_117, 4, x_102);
lean_ctor_set(x_117, 5, x_103);
x_118 = l___private_Init_Lean_Elab_Command_3__setState(x_117, x_2, x_41);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_118, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_125 = x_118;
} else {
 lean_dec_ref(x_118);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_4);
if (x_127 == 0)
{
return x_4;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_4, 0);
x_129 = lean_ctor_get(x_4, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_4);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_8 = l_Lean_Elab_Term_elabBinders___rarg(x_6, x_7, x_3, x_4);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_box(0);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__1___boxed), 4, 1);
lean_closure_set(x_7, 0, x_5);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_9);
x_12 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_2, x_9, x_6);
x_13 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_9);
lean_dec(x_9);
x_14 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_7, x_12, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_2);
x_16 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_18, 0);
lean_dec(x_24);
lean_ctor_set(x_18, 2, x_20);
lean_ctor_set(x_18, 0, x_21);
lean_inc(x_2);
x_25 = l___private_Init_Lean_Elab_Command_3__setState(x_18, x_2, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_5, x_2, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_20);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_34);
lean_ctor_set(x_36, 5, x_35);
lean_inc(x_2);
x_37 = l___private_Init_Lean_Elab_Command_3__setState(x_36, x_2, x_19);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_5, x_2, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
lean_dec(x_2);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_42 = x_37;
} else {
 lean_dec_ref(x_37);
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
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_2);
x_51 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_49, 2);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_53, 0);
lean_dec(x_59);
lean_ctor_set(x_53, 2, x_55);
lean_ctor_set(x_53, 0, x_56);
x_60 = l___private_Init_Lean_Elab_Command_3__setState(x_53, x_2, x_54);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_50);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_53, 1);
x_70 = lean_ctor_get(x_53, 3);
x_71 = lean_ctor_get(x_53, 4);
x_72 = lean_ctor_get(x_53, 5);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_53);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_56);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_55);
lean_ctor_set(x_73, 3, x_70);
lean_ctor_set(x_73, 4, x_71);
lean_ctor_set(x_73, 5, x_72);
x_74 = l___private_Init_Lean_Elab_Command_3__setState(x_73, x_2, x_54);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_50);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_50);
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_51);
if (x_82 == 0)
{
return x_51;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_51, 0);
x_84 = lean_ctor_get(x_51, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_51);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_14);
x_86 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_87 = l_unreachable_x21___rarg(x_86);
lean_inc(x_2);
x_88 = lean_apply_2(x_87, x_2, x_10);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_5, x_2, x_89);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_5);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_8);
if (x_95 == 0)
{
return x_8;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_8, 0);
x_97 = lean_ctor_get(x_8, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_8);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariable___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabVariable(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabVariable");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_40, 6);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_48, x_47);
lean_ctor_set(x_40, 6, x_49);
x_50 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_40, 0);
x_62 = lean_ctor_get(x_40, 1);
x_63 = lean_ctor_get(x_40, 2);
x_64 = lean_ctor_get(x_40, 3);
x_65 = lean_ctor_get(x_40, 4);
x_66 = lean_ctor_get(x_40, 5);
x_67 = lean_ctor_get(x_40, 6);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_40);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_68, x_67);
x_70 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set(x_70, 2, x_63);
lean_ctor_set(x_70, 3, x_64);
lean_ctor_set(x_70, 4, x_65);
lean_ctor_set(x_70, 5, x_66);
lean_ctor_set(x_70, 6, x_69);
lean_ctor_set(x_6, 0, x_70);
x_71 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_ctor_get(x_6, 1);
lean_inc(x_80);
lean_dec(x_6);
x_81 = lean_ctor_get(x_40, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_40, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_40, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_40, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_40, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_40, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_40, 6);
lean_inc(x_87);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_88 = x_40;
} else {
 lean_dec_ref(x_40);
 x_88 = lean_box(0);
}
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_89, x_87);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 7, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_82);
lean_ctor_set(x_91, 2, x_83);
lean_ctor_set(x_91, 3, x_84);
lean_ctor_set(x_91, 4, x_85);
lean_ctor_set(x_91, 5, x_86);
lean_ctor_set(x_91, 6, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_80);
lean_ctor_set(x_5, 3, x_92);
x_93 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_102 = lean_ctor_get(x_5, 0);
x_103 = lean_ctor_get(x_5, 1);
x_104 = lean_ctor_get(x_5, 2);
x_105 = lean_ctor_get(x_5, 4);
x_106 = lean_ctor_get(x_5, 5);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_5);
x_107 = lean_ctor_get(x_6, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_108 = x_6;
} else {
 lean_dec_ref(x_6);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_40, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_40, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_40, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_40, 5);
lean_inc(x_114);
x_115 = lean_ctor_get(x_40, 6);
lean_inc(x_115);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_116 = x_40;
} else {
 lean_dec_ref(x_40);
 x_116 = lean_box(0);
}
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_117, x_115);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 7, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_110);
lean_ctor_set(x_119, 2, x_111);
lean_ctor_set(x_119, 3, x_112);
lean_ctor_set(x_119, 4, x_113);
lean_ctor_set(x_119, 5, x_114);
lean_ctor_set(x_119, 6, x_118);
if (lean_is_scalar(x_108)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_108;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_107);
x_121 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_121, 0, x_102);
lean_ctor_set(x_121, 1, x_103);
lean_ctor_set(x_121, 2, x_104);
lean_ctor_set(x_121, 3, x_120);
lean_ctor_set(x_121, 4, x_105);
lean_ctor_set(x_121, 5, x_106);
x_122 = l___private_Init_Lean_Elab_Command_3__setState(x_121, x_2, x_41);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
x_125 = lean_box(0);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_2);
x_131 = !lean_is_exclusive(x_4);
if (x_131 == 0)
{
return x_4;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_4, 0);
x_133 = lean_ctor_get(x_4, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_4);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_6 = l_Lean_Elab_Term_elabBinders___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabVariables(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___lambda__1___boxed), 4, 1);
lean_closure_set(x_8, 0, x_6);
lean_inc(x_2);
x_9 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_10);
x_13 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_2, x_10, x_7);
x_14 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_10);
lean_dec(x_10);
x_15 = l_Lean_Elab_Term_elabBinders___rarg(x_12, x_8, x_13, x_14);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
x_17 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
lean_ctor_set(x_19, 2, x_21);
lean_ctor_set(x_19, 0, x_22);
lean_inc(x_2);
x_26 = l___private_Init_Lean_Elab_Command_3__setState(x_19, x_2, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_6, x_2, x_27);
lean_dec(x_6);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
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
x_33 = lean_ctor_get(x_19, 1);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_ctor_get(x_19, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_21);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_36);
lean_inc(x_2);
x_38 = l___private_Init_Lean_Elab_Command_3__setState(x_37, x_2, x_20);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_6, x_2, x_39);
lean_dec(x_6);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec(x_2);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
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
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_6);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
lean_dec(x_15);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_2);
x_52 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_50, 2);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
lean_ctor_set(x_54, 2, x_56);
lean_ctor_set(x_54, 0, x_57);
x_61 = l___private_Init_Lean_Elab_Command_3__setState(x_54, x_2, x_55);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_51);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_51);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_54, 1);
x_71 = lean_ctor_get(x_54, 3);
x_72 = lean_ctor_get(x_54, 4);
x_73 = lean_ctor_get(x_54, 5);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_74 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_74, 0, x_57);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_56);
lean_ctor_set(x_74, 3, x_71);
lean_ctor_set(x_74, 4, x_72);
lean_ctor_set(x_74, 5, x_73);
x_75 = l___private_Init_Lean_Elab_Command_3__setState(x_74, x_2, x_55);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_51);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_51);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_52);
if (x_83 == 0)
{
return x_52;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_52, 0);
x_85 = lean_ctor_get(x_52, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_52);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_15);
x_87 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_88 = l_unreachable_x21___rarg(x_87);
lean_inc(x_2);
x_89 = lean_apply_2(x_88, x_2, x_11);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_6, x_2, x_90);
lean_dec(x_6);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_6);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_9);
if (x_96 == 0)
{
return x_9;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_9, 0);
x_98 = lean_ctor_get(x_9, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_9);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariables___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabVariables(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabVariables");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_variables___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_5);
x_8 = l_Lean_Elab_Term_elabTermAux___main(x_1, x_7, x_2, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_5);
x_13 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(x_11, x_12, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_9);
x_15 = l_Lean_Elab_Term_inferType(x_3, x_9, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_9);
x_19 = l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__5;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = 0;
x_24 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_3, x_23, x_22, x_5, x_17);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_12);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
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
lean_dec(x_9);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
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
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___lambda__1___boxed), 6, 3);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_1);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_9);
x_12 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_2, x_9, x_6);
x_13 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_9);
lean_dec(x_9);
x_14 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_7, x_12, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
lean_ctor_set(x_19, 2, x_21);
lean_ctor_set(x_19, 0, x_22);
x_26 = l___private_Init_Lean_Elab_Command_3__setState(x_19, x_2, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_15);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_19, 1);
x_36 = lean_ctor_get(x_19, 3);
x_37 = lean_ctor_get(x_19, 4);
x_38 = lean_ctor_get(x_19, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_21);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_37);
lean_ctor_set(x_39, 5, x_38);
x_40 = l___private_Init_Lean_Elab_Command_3__setState(x_39, x_2, x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_15);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
return x_17;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_17, 0);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_17);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_dec(x_14);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_2);
x_55 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec(x_56);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
lean_ctor_set(x_57, 2, x_59);
lean_ctor_set(x_57, 0, x_60);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_57, x_2, x_58);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_54);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_54);
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_57, 1);
x_74 = lean_ctor_get(x_57, 3);
x_75 = lean_ctor_get(x_57, 4);
x_76 = lean_ctor_get(x_57, 5);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_57);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_60);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_59);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set(x_77, 5, x_76);
x_78 = l___private_Init_Lean_Elab_Command_3__setState(x_77, x_2, x_58);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
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
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
 lean_ctor_set_tag(x_81, 1);
}
lean_ctor_set(x_81, 0, x_54);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_54);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_55);
if (x_86 == 0)
{
return x_55;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_55, 0);
x_88 = lean_ctor_get(x_55, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_55);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_14);
x_90 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_91 = l_unreachable_x21___rarg(x_90);
x_92 = lean_apply_2(x_91, x_2, x_10);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_7);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_8);
if (x_93 == 0)
{
return x_8;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_8, 0);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_8);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_elabCheck___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabCheck");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = 1;
lean_inc(x_4);
x_8 = l_Lean_Elab_Term_elabTermAux___main(x_6, x_7, x_1, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = lean_box(0);
lean_inc(x_4);
x_13 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_10__synthesizeSyntheticMVarsAux___main(x_11, x_12, x_4, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_4);
x_15 = l_Lean_Elab_Term_instantiateMVars(x_2, x_9, x_4, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 4);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_17, 4, x_22);
x_23 = l_Lean_Meta_synthInstance(x_18, x_21, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_25, x_20);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = 0;
x_29 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_2, x_28, x_27, x_4, x_26);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_12);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_4);
x_37 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_2, x_35);
x_38 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_36, x_20);
lean_ctor_set(x_23, 1, x_38);
lean_ctor_set(x_23, 0, x_37);
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
lean_inc(x_4);
x_41 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_2, x_39);
x_42 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_40, x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
x_46 = lean_ctor_get(x_17, 2);
x_47 = lean_ctor_get(x_17, 3);
x_48 = lean_ctor_get(x_17, 4);
x_49 = lean_ctor_get(x_17, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
x_51 = l_Lean_TraceState_Inhabited___closed__1;
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_49);
x_53 = l_Lean_Meta_synthInstance(x_18, x_50, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_4);
x_56 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_55, x_48);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_58 = 0;
x_59 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_2, x_58, x_57, x_4, x_56);
lean_dec(x_4);
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
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_65 = x_53;
} else {
 lean_dec_ref(x_53);
 x_65 = lean_box(0);
}
lean_inc(x_4);
x_66 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_2, x_63);
x_67 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_2, x_4, x_16, x_64, x_48);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_9);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
return x_13;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_13, 0);
x_71 = lean_ctor_get(x_13, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_13);
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
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_8);
if (x_73 == 0)
{
return x_8;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_8, 0);
x_75 = lean_ctor_get(x_8, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_8);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_synth_cmd");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSynth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSynth___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSynth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_inc(x_2);
x_7 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_8);
x_11 = l_Lean_Elab_Command_elabSynth___closed__3;
x_12 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_2, x_8, x_11);
x_13 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_8);
lean_dec(x_8);
x_14 = l_Lean_Elab_Term_elabBinders___rarg(x_10, x_6, x_12, x_13);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
lean_ctor_set(x_19, 2, x_21);
lean_ctor_set(x_19, 0, x_22);
x_26 = l___private_Init_Lean_Elab_Command_3__setState(x_19, x_2, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_15);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_19, 1);
x_36 = lean_ctor_get(x_19, 3);
x_37 = lean_ctor_get(x_19, 4);
x_38 = lean_ctor_get(x_19, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_21);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_37);
lean_ctor_set(x_39, 5, x_38);
x_40 = l___private_Init_Lean_Elab_Command_3__setState(x_39, x_2, x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_15);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
return x_17;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_17, 0);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_17);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_dec(x_14);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_2);
x_55 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_9);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec(x_56);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
lean_ctor_set(x_57, 2, x_59);
lean_ctor_set(x_57, 0, x_60);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_57, x_2, x_58);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_54);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_54);
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_57, 1);
x_74 = lean_ctor_get(x_57, 3);
x_75 = lean_ctor_get(x_57, 4);
x_76 = lean_ctor_get(x_57, 5);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_57);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_60);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_59);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set(x_77, 5, x_76);
x_78 = l___private_Init_Lean_Elab_Command_3__setState(x_77, x_2, x_58);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
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
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
 lean_ctor_set_tag(x_81, 1);
}
lean_ctor_set(x_81, 0, x_54);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_54);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_55);
if (x_86 == 0)
{
return x_55;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_55, 0);
x_88 = lean_ctor_get(x_55, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_55);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_14);
x_90 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_91 = l_unreachable_x21___rarg(x_90);
x_92 = lean_apply_2(x_91, x_2, x_9);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_6);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_7);
if (x_93 == 0)
{
return x_7;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_7, 0);
x_95 = lean_ctor_get(x_7, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_7);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabSynth___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSynth");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_synth___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 3);
lean_dec(x_10);
x_11 = l_Lean_Elab_Command_modifyScope___closed__1;
x_12 = l_unreachable_x21___rarg(x_11);
lean_ctor_set(x_6, 3, x_12);
x_13 = l___private_Init_Lean_Elab_Command_3__setState(x_6, x_3, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
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
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
x_26 = lean_ctor_get(x_6, 2);
x_27 = lean_ctor_get(x_6, 4);
x_28 = lean_ctor_get(x_6, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_29 = l_Lean_Elab_Command_modifyScope___closed__1;
x_30 = l_unreachable_x21___rarg(x_29);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
x_32 = l___private_Init_Lean_Elab_Command_3__setState(x_31, x_3, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
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
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 3);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_7, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 2);
x_49 = l_Lean_KVMap_insertCore___main(x_48, x_1, x_2);
lean_ctor_set(x_41, 2, x_49);
x_50 = l___private_Init_Lean_Elab_Command_3__setState(x_6, x_3, x_42);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_41, 0);
x_62 = lean_ctor_get(x_41, 1);
x_63 = lean_ctor_get(x_41, 2);
x_64 = lean_ctor_get(x_41, 3);
x_65 = lean_ctor_get(x_41, 4);
x_66 = lean_ctor_get(x_41, 5);
x_67 = lean_ctor_get(x_41, 6);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_41);
x_68 = l_Lean_KVMap_insertCore___main(x_63, x_1, x_2);
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set(x_69, 4, x_65);
lean_ctor_set(x_69, 5, x_66);
lean_ctor_set(x_69, 6, x_67);
lean_ctor_set(x_7, 0, x_69);
x_70 = l___private_Init_Lean_Elab_Command_3__setState(x_6, x_3, x_42);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_7, 1);
lean_inc(x_79);
lean_dec(x_7);
x_80 = lean_ctor_get(x_41, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_41, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_41, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_41, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_41, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_41, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_41, 6);
lean_inc(x_86);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_87 = x_41;
} else {
 lean_dec_ref(x_41);
 x_87 = lean_box(0);
}
x_88 = l_Lean_KVMap_insertCore___main(x_82, x_1, x_2);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 7, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_84);
lean_ctor_set(x_89, 5, x_85);
lean_ctor_set(x_89, 6, x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_79);
lean_ctor_set(x_6, 3, x_90);
x_91 = l___private_Init_Lean_Elab_Command_3__setState(x_6, x_3, x_42);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_100 = lean_ctor_get(x_6, 0);
x_101 = lean_ctor_get(x_6, 1);
x_102 = lean_ctor_get(x_6, 2);
x_103 = lean_ctor_get(x_6, 4);
x_104 = lean_ctor_get(x_6, 5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_6);
x_105 = lean_ctor_get(x_7, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_106 = x_7;
} else {
 lean_dec_ref(x_7);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_41, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_41, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_41, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_41, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_41, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_41, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_41, 6);
lean_inc(x_113);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_114 = x_41;
} else {
 lean_dec_ref(x_41);
 x_114 = lean_box(0);
}
x_115 = l_Lean_KVMap_insertCore___main(x_109, x_1, x_2);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 7, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_108);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set(x_116, 4, x_111);
lean_ctor_set(x_116, 5, x_112);
lean_ctor_set(x_116, 6, x_113);
if (lean_is_scalar(x_106)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_106;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_105);
x_118 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_118, 0, x_100);
lean_ctor_set(x_118, 1, x_101);
lean_ctor_set(x_118, 2, x_102);
lean_ctor_set(x_118, 3, x_117);
lean_ctor_set(x_118, 4, x_103);
lean_ctor_set(x_118, 5, x_104);
x_119 = l___private_Init_Lean_Elab_Command_3__setState(x_118, x_3, x_42);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_126 = x_119;
} else {
 lean_dec_ref(x_119);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_5);
if (x_128 == 0)
{
return x_5;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_5, 0);
x_130 = lean_ctor_get(x_5, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_5);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_setOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch at set_option");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_setOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_setOption___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_setOption___closed__3() {
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
lean_object* x_6; lean_object* x_102; 
lean_inc(x_2);
x_102 = l_Lean_getOptionDecl(x_2, x_5);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_DataValue_sameCtor(x_105, x_3);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_3);
lean_dec(x_2);
x_107 = l_Lean_Elab_Command_setOption___closed__3;
x_108 = l_Lean_Elab_Command_throwError___rarg(x_1, x_107, x_4, x_104);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
return x_108;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
x_6 = x_104;
goto block_101;
}
}
else
{
uint8_t x_113; 
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_102);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_102, 0);
x_115 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_4, x_1, x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_102, 0, x_116);
return x_102;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_102, 0);
x_118 = lean_ctor_get(x_102, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_102);
x_119 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_4, x_1, x_117);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
}
block_101:
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(x_2, x_3, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
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
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_getMaxRecDepth___closed__1;
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_7);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_4);
x_17 = l___private_Init_Lean_Elab_Command_2__getState(x_4, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 5);
lean_dec(x_21);
lean_ctor_set(x_18, 5, x_16);
x_22 = l___private_Init_Lean_Elab_Command_3__setState(x_18, x_4, x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
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
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_ctor_get(x_18, 2);
x_36 = lean_ctor_get(x_18, 3);
x_37 = lean_ctor_get(x_18, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_16);
x_39 = l___private_Init_Lean_Elab_Command_3__setState(x_38, x_4, x_19);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_16);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
return x_17;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_17, 0);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_17);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_box(0);
lean_ctor_set(x_7, 0, x_52);
return x_7;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_dec(x_7);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_dec(x_2);
x_55 = l_Lean_getMaxRecDepth___closed__1;
x_56 = lean_string_dec_eq(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
else
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
lean_dec(x_3);
lean_inc(x_4);
x_60 = l___private_Init_Lean_Elab_Command_2__getState(x_4, x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 4);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_59);
x_70 = l___private_Init_Lean_Elab_Command_3__setState(x_69, x_4, x_62);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_59);
lean_dec(x_4);
x_79 = lean_ctor_get(x_60, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_81 = x_60;
} else {
 lean_dec_ref(x_60);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_53);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_7);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_7, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_7, 0, x_87);
return x_7;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_7, 1);
lean_inc(x_88);
lean_dec(x_7);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_7);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_7, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_7, 0, x_93);
return x_7;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_7, 1);
lean_inc(x_94);
lean_dec(x_7);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_7);
if (x_97 == 0)
{
return x_7;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_7, 0);
x_99 = lean_ctor_get(x_7, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_7);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_setOption(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected set_option value ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSetOption___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSetOption___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_21; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getIdAt(x_1, x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_21 = l_Lean_Syntax_isStrLit_x3f(x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_numLitKind;
x_23 = l_Lean_Syntax_isNatLitAux(x_22, x_7);
if (lean_obj_tag(x_23) == 0)
{
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
x_25 = l_Bool_HasRepr___closed__2;
x_26 = lean_string_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Bool_HasRepr___closed__1;
x_28 = lean_string_dec_eq(x_24, x_27);
lean_dec(x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_5);
x_29 = lean_box(0);
x_8 = x_29;
goto block_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
x_30 = l_Lean_registerTraceClass___closed__1;
x_31 = l_Lean_Elab_Command_setOption(x_1, x_5, x_30, x_2, x_3);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_7);
x_32 = l_Lean_verboseOption___closed__3;
x_33 = l_Lean_Elab_Command_setOption(x_1, x_5, x_32, x_2, x_3);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_5);
x_34 = lean_box(0);
x_8 = x_34;
goto block_20;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_Elab_Command_setOption(x_1, x_5, x_36, x_2, x_3);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Elab_Command_setOption(x_1, x_5, x_39, x_2, x_3);
return x_40;
}
block_20:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_11 = l_Lean_Syntax_formatStxAux___main(x_9, x_10, x_7);
x_12 = l_Lean_Options_empty;
x_13 = l_Lean_Format_pretty(x_11, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Command_elabSetOption___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = 2;
x_19 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_7, x_18, x_17, x_2, x_3);
lean_dec(x_7);
return x_19;
}
}
}
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabSetOption(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSetOption");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_set__option___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_40, 5);
lean_dec(x_47);
lean_ctor_set(x_40, 5, x_1);
x_48 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
x_61 = lean_ctor_get(x_40, 2);
x_62 = lean_ctor_get(x_40, 3);
x_63 = lean_ctor_get(x_40, 4);
x_64 = lean_ctor_get(x_40, 6);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_65 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_1);
lean_ctor_set(x_65, 6, x_64);
lean_ctor_set(x_6, 0, x_65);
x_66 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_6, 1);
lean_inc(x_75);
lean_dec(x_6);
x_76 = lean_ctor_get(x_40, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_40, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_40, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_40, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 6);
lean_inc(x_81);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_82 = x_40;
} else {
 lean_dec_ref(x_40);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 7, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set(x_83, 4, x_80);
lean_ctor_set(x_83, 5, x_1);
lean_ctor_set(x_83, 6, x_81);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_5, 3, x_84);
x_85 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_94 = lean_ctor_get(x_5, 0);
x_95 = lean_ctor_get(x_5, 1);
x_96 = lean_ctor_get(x_5, 2);
x_97 = lean_ctor_get(x_5, 4);
x_98 = lean_ctor_get(x_5, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_5);
x_99 = lean_ctor_get(x_6, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_100 = x_6;
} else {
 lean_dec_ref(x_6);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_40, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_40, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_40, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_40, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_40, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 6);
lean_inc(x_106);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_107 = x_40;
} else {
 lean_dec_ref(x_40);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 7, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_105);
lean_ctor_set(x_108, 5, x_1);
lean_ctor_set(x_108, 6, x_106);
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
x_110 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_95);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_109);
lean_ctor_set(x_110, 4, x_97);
lean_ctor_set(x_110, 5, x_98);
x_111 = l___private_Init_Lean_Elab_Command_3__setState(x_110, x_2, x_41);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
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
else
{
uint8_t x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_4);
if (x_120 == 0)
{
return x_4;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_4, 0);
x_122 = lean_ctor_get(x_4, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_4);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_40, 5);
lean_dec(x_47);
lean_ctor_set(x_40, 5, x_1);
x_48 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
x_61 = lean_ctor_get(x_40, 2);
x_62 = lean_ctor_get(x_40, 3);
x_63 = lean_ctor_get(x_40, 4);
x_64 = lean_ctor_get(x_40, 6);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_65 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_1);
lean_ctor_set(x_65, 6, x_64);
lean_ctor_set(x_6, 0, x_65);
x_66 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_6, 1);
lean_inc(x_75);
lean_dec(x_6);
x_76 = lean_ctor_get(x_40, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_40, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_40, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_40, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 6);
lean_inc(x_81);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_82 = x_40;
} else {
 lean_dec_ref(x_40);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 7, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set(x_83, 4, x_80);
lean_ctor_set(x_83, 5, x_1);
lean_ctor_set(x_83, 6, x_81);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_5, 3, x_84);
x_85 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_94 = lean_ctor_get(x_5, 0);
x_95 = lean_ctor_get(x_5, 1);
x_96 = lean_ctor_get(x_5, 2);
x_97 = lean_ctor_get(x_5, 4);
x_98 = lean_ctor_get(x_5, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_5);
x_99 = lean_ctor_get(x_6, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_100 = x_6;
} else {
 lean_dec_ref(x_6);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_40, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_40, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_40, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_40, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_40, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 6);
lean_inc(x_106);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_107 = x_40;
} else {
 lean_dec_ref(x_40);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 7, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_105);
lean_ctor_set(x_108, 5, x_1);
lean_ctor_set(x_108, 6, x_106);
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
x_110 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_95);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_109);
lean_ctor_set(x_110, 4, x_97);
lean_ctor_set(x_110, 5, x_98);
x_111 = l___private_Init_Lean_Elab_Command_3__setState(x_110, x_2, x_41);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
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
else
{
uint8_t x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_4);
if (x_120 == 0)
{
return x_4;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_4, 0);
x_122 = lean_ctor_get(x_4, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_4);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_40, 5);
lean_dec(x_47);
lean_ctor_set(x_40, 5, x_1);
x_48 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
x_61 = lean_ctor_get(x_40, 2);
x_62 = lean_ctor_get(x_40, 3);
x_63 = lean_ctor_get(x_40, 4);
x_64 = lean_ctor_get(x_40, 6);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_65 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_1);
lean_ctor_set(x_65, 6, x_64);
lean_ctor_set(x_6, 0, x_65);
x_66 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_6, 1);
lean_inc(x_75);
lean_dec(x_6);
x_76 = lean_ctor_get(x_40, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_40, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_40, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_40, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 6);
lean_inc(x_81);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_82 = x_40;
} else {
 lean_dec_ref(x_40);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 7, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set(x_83, 4, x_80);
lean_ctor_set(x_83, 5, x_1);
lean_ctor_set(x_83, 6, x_81);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_5, 3, x_84);
x_85 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_94 = lean_ctor_get(x_5, 0);
x_95 = lean_ctor_get(x_5, 1);
x_96 = lean_ctor_get(x_5, 2);
x_97 = lean_ctor_get(x_5, 4);
x_98 = lean_ctor_get(x_5, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_5);
x_99 = lean_ctor_get(x_6, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_100 = x_6;
} else {
 lean_dec_ref(x_6);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_40, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_40, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_40, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_40, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_40, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 6);
lean_inc(x_106);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_107 = x_40;
} else {
 lean_dec_ref(x_40);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 7, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_105);
lean_ctor_set(x_108, 5, x_1);
lean_ctor_set(x_108, 6, x_106);
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
x_110 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_95);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_109);
lean_ctor_set(x_110, 4, x_97);
lean_ctor_set(x_110, 5, x_98);
x_111 = l___private_Init_Lean_Elab_Command_3__setState(x_110, x_2, x_41);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
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
else
{
uint8_t x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_4);
if (x_120 == 0)
{
return x_4;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_4, 0);
x_122 = lean_ctor_get(x_4, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_4);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 3);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 3, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
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
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_28 = l_Lean_Elab_Command_modifyScope___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
x_31 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_5, 3);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_6, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_40, 5);
lean_dec(x_47);
lean_ctor_set(x_40, 5, x_1);
x_48 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
x_61 = lean_ctor_get(x_40, 2);
x_62 = lean_ctor_get(x_40, 3);
x_63 = lean_ctor_get(x_40, 4);
x_64 = lean_ctor_get(x_40, 6);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
x_65 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_1);
lean_ctor_set(x_65, 6, x_64);
lean_ctor_set(x_6, 0, x_65);
x_66 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_6, 1);
lean_inc(x_75);
lean_dec(x_6);
x_76 = lean_ctor_get(x_40, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_40, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_40, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_40, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_40, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_40, 6);
lean_inc(x_81);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_82 = x_40;
} else {
 lean_dec_ref(x_40);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 7, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set(x_83, 4, x_80);
lean_ctor_set(x_83, 5, x_1);
lean_ctor_set(x_83, 6, x_81);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_5, 3, x_84);
x_85 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_41);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_94 = lean_ctor_get(x_5, 0);
x_95 = lean_ctor_get(x_5, 1);
x_96 = lean_ctor_get(x_5, 2);
x_97 = lean_ctor_get(x_5, 4);
x_98 = lean_ctor_get(x_5, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_5);
x_99 = lean_ctor_get(x_6, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_100 = x_6;
} else {
 lean_dec_ref(x_6);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_40, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_40, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_40, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_40, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_40, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 6);
lean_inc(x_106);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 x_107 = x_40;
} else {
 lean_dec_ref(x_40);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 7, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_103);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_105);
lean_ctor_set(x_108, 5, x_1);
lean_ctor_set(x_108, 6, x_106);
if (lean_is_scalar(x_100)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_100;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_99);
x_110 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_95);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_109);
lean_ctor_set(x_110, 4, x_97);
lean_ctor_set(x_110, 5, x_98);
x_111 = l___private_Init_Lean_Elab_Command_3__setState(x_110, x_2, x_41);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
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
else
{
uint8_t x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_4);
if (x_120 == 0)
{
return x_4;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_4, 0);
x_122 = lean_ctor_get(x_4, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_4);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Syntax_getId(x_10);
x_14 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(x_13, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
x_3 = x_12;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_4);
x_17 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_10, x_13, x_5, x_6);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_withDeclId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid declaration name");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_withDeclId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withDeclId___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_withDeclId___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withDeclId___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withDeclId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getIdAt(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_inc(x_3);
x_9 = l_Lean_Elab_Command_getLevelNames(x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_104; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_104 = l_Lean_Syntax_isNone(x_8);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_106 = l_Lean_Syntax_getArgs(x_105);
lean_dec(x_105);
x_107 = lean_unsigned_to_nat(2u);
x_108 = l_Array_empty___closed__1;
x_109 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_107, x_106, x_5, x_108);
lean_dec(x_106);
lean_inc(x_3);
lean_inc(x_10);
x_110 = l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(x_1, x_109, x_5, x_10, x_3, x_11);
lean_dec(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_12 = x_111;
x_13 = x_112;
goto block_103;
}
else
{
uint8_t x_113; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 0);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_110);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_dec(x_8);
lean_inc(x_10);
x_12 = x_10;
x_13 = x_11;
goto block_103;
}
block_103:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_extractMacroScopes(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_name_mk_string(x_20, x_19);
x_22 = l_Lean_addMacroScopes(x_16, x_21, x_17);
x_23 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_24 = 1;
lean_inc(x_3);
lean_inc(x_18);
x_25 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_1, x_23, x_24, x_18, x_3, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_3);
x_27 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(x_12, x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_3);
x_29 = lean_apply_3(x_2, x_22, x_3, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_3);
lean_inc(x_10);
x_32 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(x_10, x_3, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_3);
x_34 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 3);
x_39 = l_Lean_Name_getNumParts___main(x_18);
lean_dec(x_18);
x_40 = l_List_drop___main___rarg(x_39, x_38);
lean_dec(x_38);
lean_ctor_set(x_35, 3, x_40);
x_41 = l___private_Init_Lean_Elab_Command_3__setState(x_35, x_3, x_36);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_30);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_30);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
x_52 = lean_ctor_get(x_35, 2);
x_53 = lean_ctor_get(x_35, 3);
x_54 = lean_ctor_get(x_35, 4);
x_55 = lean_ctor_get(x_35, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_56 = l_Lean_Name_getNumParts___main(x_18);
lean_dec(x_18);
x_57 = l_List_drop___main___rarg(x_56, x_53);
lean_dec(x_53);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
x_59 = l___private_Init_Lean_Elab_Command_3__setState(x_58, x_3, x_36);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
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
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_30);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_30);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
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
uint8_t x_67; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
return x_34;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_34, 0);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_34);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_30);
lean_dec(x_18);
x_71 = lean_ctor_get(x_32, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_32, 1);
lean_inc(x_72);
lean_dec(x_32);
x_73 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(x_10, x_3, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_71);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
return x_73;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_73, 0);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_73);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_18);
x_82 = lean_ctor_get(x_29, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_29, 1);
lean_inc(x_83);
lean_dec(x_29);
x_84 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(x_10, x_3, x_83);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
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
else
{
uint8_t x_89; 
lean_dec(x_82);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_27);
if (x_93 == 0)
{
return x_27;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_27, 0);
x_95 = lean_ctor_get(x_27, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_27);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_25);
if (x_97 == 0)
{
return x_25;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_25, 0);
x_99 = lean_ctor_get(x_25, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_25);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
x_101 = l_Lean_Elab_Command_withDeclId___closed__3;
x_102 = l_Lean_Elab_Command_throwError___rarg(x_1, x_101, x_3, x_13);
return x_102;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_9);
if (x_117 == 0)
{
return x_9;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_9, 0);
x_119 = lean_ctor_get(x_9, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_9);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_withDeclId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_withDeclId(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_5);
if (x_7 == 0)
{
lean_free_object(x_3);
lean_dec(x_5);
x_3 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_2);
x_2 = x_3;
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_10);
if (x_12 == 0)
{
lean_dec(x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_2);
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
}
}
}
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_fswap(x_2, x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_2 = x_15;
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_swap(x_3, x_4, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Name_inhabited;
x_10 = lean_array_get(x_9, x_3, x_5);
x_11 = l_Lean_Name_lt___main(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_swap(x_3, x_4, x_5);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_18 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_3 = x_15;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_37 = l_Lean_Name_inhabited;
x_38 = lean_array_get(x_37, x_1, x_16);
x_39 = lean_array_get(x_37, x_1, x_2);
x_40 = l_Lean_Name_lt___main(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
x_17 = x_1;
goto block_36;
}
else
{
lean_object* x_41; 
x_41 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_41;
goto block_36;
}
block_36:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Name_inhabited;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = l_Lean_Name_lt___main(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get(x_18, x_17, x_16);
x_23 = l_Lean_Name_lt___main(x_22, x_19);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_24 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_19, x_17, x_2, x_2);
lean_dec(x_19);
x_4 = x_24;
goto block_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
x_25 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_26 = lean_array_get(x_18, x_25, x_3);
lean_inc_n(x_2, 2);
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_26, x_25, x_2, x_2);
lean_dec(x_26);
x_4 = x_27;
goto block_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_19);
x_28 = lean_array_swap(x_17, x_2, x_3);
x_29 = lean_array_get(x_18, x_28, x_16);
x_30 = lean_array_get(x_18, x_28, x_3);
x_31 = l_Lean_Name_lt___main(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_32 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_30, x_28, x_2, x_2);
lean_dec(x_30);
x_4 = x_32;
goto block_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
x_33 = lean_array_swap(x_28, x_16, x_3);
lean_dec(x_16);
x_34 = lean_array_get(x_18, x_33, x_3);
lean_inc_n(x_2, 2);
x_35 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_3, x_34, x_33, x_2, x_2);
lean_dec(x_34);
x_4 = x_35;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
lean_inc(x_1);
x_4 = l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(x_2, x_3, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(x_1, x_2, x_5, x_5);
lean_dec(x_1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(x_6, x_5, x_9);
lean_dec(x_9);
x_11 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
x_12 = l_List_append___rarg(x_4, x_11);
return x_12;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Command_getEnv(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_add_decl(x_6, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_3);
x_10 = l_Lean_Elab_Command_getOptions(x_3, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_KernelException_toMessageData(x_9, x_11);
x_14 = l_Lean_Elab_Command_throwError___rarg(x_1, x_13, x_3, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_3);
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
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lean_Elab_Command_setEnv(x_19, x_3, x_7);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_compileDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Command_getEnv(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Elab_Command_getOptions(x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_compile_decl(x_6, x_9, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_KernelException_toMessageData(x_12, x_9);
x_14 = l_Lean_Elab_Command_throwError___rarg(x_1, x_13, x_3, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Elab_Command_setEnv(x_15, x_3, x_10);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_compileDecl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object*);
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_TermBinders(lean_object*);
lean_object* initialize_Init_Lean_Elab_SynthesizeSyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Command(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_TermBinders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_SynthesizeSyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_Scope_inhabited___closed__1 = _init_l_Lean_Elab_Command_Scope_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Scope_inhabited___closed__1);
l_Lean_Elab_Command_Scope_inhabited = _init_l_Lean_Elab_Command_Scope_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_Scope_inhabited);
l_Lean_Elab_Command_State_inhabited___closed__1 = _init_l_Lean_Elab_Command_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__1);
l_Lean_Elab_Command_State_inhabited___closed__2 = _init_l_Lean_Elab_Command_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__2);
l_Lean_Elab_Command_State_inhabited___closed__3 = _init_l_Lean_Elab_Command_State_inhabited___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__3);
l_Lean_Elab_Command_State_inhabited___closed__4 = _init_l_Lean_Elab_Command_State_inhabited___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited___closed__4);
l_Lean_Elab_Command_State_inhabited = _init_l_Lean_Elab_Command_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_State_inhabited);
l_Lean_Elab_Command_Exception_inhabited = _init_l_Lean_Elab_Command_Exception_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_Exception_inhabited);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3);
l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4 = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4);
l_Lean_Elab_Command_CommandElabCoreM_monadState = _init_l_Lean_Elab_Command_CommandElabCoreM_monadState();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabCoreM_monadState);
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
l_Lean_Elab_Command_CommandElabM_monadLog___closed__8 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__8);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__9 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__9);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__10 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__10);
l_Lean_Elab_Command_CommandElabM_monadLog___closed__11 = _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog___closed__11);
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
l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3 = _init_l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1);
res = l_Lean_Elab_Command_mkBuiltinCommandElabTable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_builtinCommandElabTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_builtinCommandElabTable);
lean_dec_ref(res);
l_Lean_Elab_Command_addBuiltinCommandElab___closed__1 = _init_l_Lean_Elab_Command_addBuiltinCommandElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_addBuiltinCommandElab___closed__1);
l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1 = _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1);
l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2 = _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2);
l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3 = _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3);
l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4 = _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4);
l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5 = _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5);
l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6 = _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6);
l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7 = _init_l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__5 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__5);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5);
res = l_Lean_Elab_Command_registerBuiltinCommandElabAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__1 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__1);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__2 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__2);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__3 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__3);
l_Lean_Elab_Command_commandElabAttribute___closed__1 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__1);
l_Lean_Elab_Command_commandElabAttribute___closed__2 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__2);
l_Lean_Elab_Command_commandElabAttribute___closed__3 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__3);
l_Lean_Elab_Command_commandElabAttribute___closed__4 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__4);
l_Lean_Elab_Command_commandElabAttribute___closed__5 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__5);
res = l_Lean_Elab_Command_mkCommandElabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_commandElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__1);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__2);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__3);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__4);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__5);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__6);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7 = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter___closed__7);
l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter = _init_l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_MonadMacroAdapter);
l_Lean_Elab_Command_elabCommand___main___closed__1 = _init_l_Lean_Elab_Command_elabCommand___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___main___closed__1);
l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_10__toCommandResult___rarg___closed__1);
l_Lean_Elab_Command_CommandElabM_inhabited___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_inhabited___closed__1);
l_Lean_Elab_Command_runTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Command_runTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_runTermElabM___rarg___closed__1);
l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__1 = _init_l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__1);
l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__2 = _init_l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__2);
l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__3 = _init_l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_12__addScopes___main___closed__3);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabSection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabEnd___closed__1 = _init_l_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__1);
l_Lean_Elab_Command_elabEnd___closed__2 = _init_l_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__2);
l_Lean_Elab_Command_elabEnd___closed__3 = _init_l_Lean_Elab_Command_elabEnd___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__3);
l_Lean_Elab_Command_elabEnd___closed__4 = _init_l_Lean_Elab_Command_elabEnd___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__4);
l_Lean_Elab_Command_elabEnd___closed__5 = _init_l_Lean_Elab_Command_elabEnd___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__5);
l_Lean_Elab_Command_elabEnd___closed__6 = _init_l_Lean_Elab_Command_elabEnd___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__6);
l_Lean_Elab_Command_elabEnd___closed__7 = _init_l_Lean_Elab_Command_elabEnd___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__7);
l_Lean_Elab_Command_elabEnd___closed__8 = _init_l_Lean_Elab_Command_elabEnd___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__8);
l_Lean_Elab_Command_elabEnd___closed__9 = _init_l_Lean_Elab_Command_elabEnd___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__9);
l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_modifyScope___closed__1 = _init_l_Lean_Elab_Command_modifyScope___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__1);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4);
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5);
l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_logUnknownDecl___closed__1 = _init_l_Lean_Elab_Command_logUnknownDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_logUnknownDecl___closed__1);
l_Lean_Elab_Command_logUnknownDecl___closed__2 = _init_l_Lean_Elab_Command_logUnknownDecl___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_logUnknownDecl___closed__2);
l_Lean_Elab_Command_elabExport___closed__1 = _init_l_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__1);
l_Lean_Elab_Command_elabExport___closed__2 = _init_l_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__2);
l_Lean_Elab_Command_elabExport___closed__3 = _init_l_Lean_Elab_Command_elabExport___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__3);
l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabExport(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3);
l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSynth___closed__1 = _init_l_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__1);
l_Lean_Elab_Command_elabSynth___closed__2 = _init_l_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__2);
l_Lean_Elab_Command_elabSynth___closed__3 = _init_l_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__3);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabSynth(lean_io_mk_world());
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
l_Lean_Elab_Command_elabSetOption___closed__3 = _init_l_Lean_Elab_Command_elabSetOption___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__3);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabSetOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_withDeclId___closed__1 = _init_l_Lean_Elab_Command_withDeclId___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_withDeclId___closed__1);
l_Lean_Elab_Command_withDeclId___closed__2 = _init_l_Lean_Elab_Command_withDeclId___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_withDeclId___closed__2);
l_Lean_Elab_Command_withDeclId___closed__3 = _init_l_Lean_Elab_Command_withDeclId___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_withDeclId___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
