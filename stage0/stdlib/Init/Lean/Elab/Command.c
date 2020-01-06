// Lean compiler output
// Module: Init.Lean.Elab.Command
// Imports: Init.Lean.Elab.Alias Init.Lean.Elab.Log Init.Lean.Elab.ResolveName Init.Lean.Elab.Term Init.Lean.Elab.TermBinders
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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4;
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSection(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace(lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__3;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_Elab_Command_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__4;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3;
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__2;
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2;
extern lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_withNamespace(lean_object*);
extern lean_object* l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__8;
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__1;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1;
lean_object* l_Lean_Environment_registerNamespace___main(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable(lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_7__regTraceClasses___closed__1;
uint8_t l_Lean_Name_lt___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIOCore(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO(lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__1;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__2;
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSection___closed__1;
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_stxInh;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__3(lean_object*, size_t, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__2;
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint___main(lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5;
lean_object* l_Lean_Elab_Command_State_inhabited___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_10__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr(lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_14__addNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addAlias(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport(lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_inhabited;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__1;
extern lean_object* l_Lean_Meta_MetaHasEval___rarg___closed__4;
extern lean_object* l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables(lean_object*);
lean_object* l_Lean_Elab_Command_elabMixfix___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwUnexpectedSyntax___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__9;
lean_object* l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__3;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd___closed__4;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1;
lean_object* l_Lean_Elab_Command_resolveNamespace___closed__2;
lean_object* l_Lean_Elab_Command_elabNotation___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__6;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_Elab_Command_resolveNamespace___closed__1;
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited(lean_object*);
lean_object* l_Lean_Elab_Command_mkBuiltinCommandElabTable(lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_11__toCommandResult(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand___closed__6;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3;
extern lean_object* l_Lean_Syntax_getKind___closed__4;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMixfix___rarg(lean_object*);
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
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
extern lean_object* l_Lean_Elab_Term_elabTerm___closed__6;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__2;
lean_object* l_Lean_Elab_Command_elabExport___closed__3;
extern lean_object* l_Lean_Parser_mkCommandParserAttribute___closed__4;
lean_object* l_Lean_Elab_Command_dbgTrace(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_5__getBetterRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__8;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
lean_object* l___private_Init_Lean_Elab_Command_4__modifyGetState(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_9__mkTermState___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5;
lean_object* l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__2(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2;
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Command_7__addMacroStack___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__3;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3;
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel(lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_15__checkAnonymousScope___boxed(lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab___closed__1;
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_15__checkAnonymousScope(lean_object*);
lean_object* l_Lean_Elab_Command_throwUnexpectedSyntax(lean_object*);
extern lean_object* l_Lean_Message_Inhabited;
lean_object* l_Lean_Elab_Command_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState;
extern lean_object* l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__3;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_11__toCommandResult___boxed(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4;
lean_object* l___private_Init_Lean_Elab_Command_1__ioErrorToMessage___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_6__prettyPrint___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses(lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__1;
extern lean_object* l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_16__checkEndHeader___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__13(lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_10__getVarDecls___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_getScopes(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_3__addMacroStack___spec__1___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2;
lean_object* l___private_Init_Lean_Elab_Command_6__prettyPrint(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_builtinCommandElabTable;
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withLogging(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2;
extern lean_object* l_Lean_Parser_registerParserAttribute___closed__5;
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Elab_Command_Scope_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__7;
lean_object* l_Lean_Elab_Command_liftIOCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5(lean_object*, size_t, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd(lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3;
extern lean_object* l_Lean_Parser_Command_notation___elambda__1___closed__2;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__4;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog;
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__3;
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabCoreM_monadState___closed__4;
lean_object* l___private_Init_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_16__checkEndHeader___main(lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__6;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2;
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReserve(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___closed__2;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_8__mkTermContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__1;
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__6;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
lean_object* l_AssocList_foldlM___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__14(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nameToExprAux___main(lean_object*);
extern lean_object* l_Lean_Parser_Command_reserve___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_1__getBetterRef___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__3;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__5;
lean_object* l_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2;
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2;
extern lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__6;
lean_object* l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__2;
lean_object* l_Lean_SMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReserve___rarg(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot(lean_object*);
lean_object* l_Lean_Elab_Command_resolveNamespace___closed__3;
lean_object* l_Lean_Elab_Command_withDeclId___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNotation(lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__2;
lean_object* l_PersistentHashMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getOpenDecls(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3;
lean_object* l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_getEnv(lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1;
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___closed__3;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Elab_Command_addBuiltinCommandElab___spec__12(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4;
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__3;
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_4__modifyGetState___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Elab_Command_sortDeclLevelParams___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setEnv(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3;
lean_object* l_Lean_Elab_Command_withDeclId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg(lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_variables___elambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Lean_Elab_Command_elabReserve___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIOCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__2;
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__10;
extern lean_object* l_Lean_Message_Inhabited___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_16__checkEndHeader___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_16__checkEndHeader(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMixfix(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_7__addMacroStack(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
lean_object* l___private_Init_Lean_Elab_Term_19__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__1;
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
lean_object* l_Lean_Elab_Command_elabEnd___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand___closed__3;
lean_object* l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Command_7__addMacroStack___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__5;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
extern lean_object* l_Lean_initAttr;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2;
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__5;
lean_object* l___private_Init_Lean_Elab_Command_9__mkTermState(lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_MonadQuotation;
lean_object* l___private_Init_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l___private_Init_Lean_Elab_Command_8__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2;
lean_object* lean_add_decl(lean_object*, lean_object*);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_EnvExtension_setState___closed__1;
x_2 = l_PersistentArray_empty___closed__3;
x_3 = l_Lean_Elab_Command_State_inhabited___closed__3;
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_box(0);
x_5 = l_Lean_Elab_Command_State_inhabited___closed__1;
x_6 = l_String_splitAux___main___closed__1;
x_7 = lean_box(0);
x_8 = l_Array_empty___closed__1;
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
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
return x_12;
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = 2;
x_7 = l_Lean_Elab_Command_mkMessageAux(x_1, x_2, x_5, x_6);
return x_7;
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_3, x_1, x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_3, x_1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_box(0);
x_12 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_11, x_10);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_1, x_15, x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_box(0);
x_13 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_12, x_11);
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
x_16 = lean_box(0);
x_17 = l___private_Init_Lean_Elab_Command_1__ioErrorToMessage(x_2, x_16, x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
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
x_4 = lean_ctor_get(x_1, 3);
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
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_PersistentArray_push___rarg(x_8, x_1);
lean_ctor_set(x_5, 1, x_9);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_25 = l_PersistentArray_push___rarg(x_22, x_1);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = l___private_Init_Lean_Elab_Command_3__setState(x_26, x_2, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
return x_4;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
x_3 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
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
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__10;
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
lean_object* l___private_Init_Lean_Elab_Command_5__getBetterRef(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Term_1__getBetterRef___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_List_find_x3f___main___rarg(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__prettyPrint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_reprint___main(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_formatStxAux___main(x_5, x_6, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__prettyPrint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Command_6__prettyPrint(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Command_7__addMacroStack___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l___private_Init_Lean_Elab_Command_6__prettyPrint(x_6, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MessageData_ofList___closed__3;
x_12 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_3__addMacroStack___spec__1___closed__3;
x_14 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_1 = x_19;
x_2 = x_7;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_7__addMacroStack(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
x_5 = l_List_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_List_foldlM___main___at___private_Init_Lean_Elab_Command_7__addMacroStack___spec__1(x_1, x_4, x_2, x_3);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Command_7__addMacroStack___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldlM___main___at___private_Init_Lean_Elab_Command_7__addMacroStack___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
x_5 = lean_ctor_get(x_2, 3);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_box(0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_FileMap_toPosition(x_7, x_8);
x_11 = l_String_splitAux___main___closed__1;
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = l_Lean_FileMap_toPosition(x_7, x_14);
x_16 = l_String_splitAux___main___closed__1;
lean_inc(x_6);
x_17 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_5 = l___private_Init_Lean_Elab_Command_5__getBetterRef(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l___private_Init_Lean_Elab_Command_7__addMacroStack(x_2, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 2;
x_12 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_throwError___spec__1(x_9, x_11, x_6, x_3, x_10);
lean_dec(x_3);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
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
}
lean_object* l_Lean_Elab_Command_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwError___rarg), 4, 0);
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
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elab_Command_6__prettyPrint(x_1, x_3, x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = l_Lean_MessageData_ofList___closed__3;
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__3;
x_14 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Command_throwError___rarg(x_1, x_14, x_3, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__6;
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__8;
x_24 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_16);
x_26 = l_Lean_MessageData_ofList___closed__3;
x_27 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Command_throwError___rarg(x_1, x_30, x_3, x_17);
return x_31;
}
}
}
lean_object* l_Lean_Elab_Command_throwUnexpectedSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwUnexpectedSyntax___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_throwUnexpectedSyntax___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 5);
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
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_ctor_set(x_5, 3, x_10);
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
x_14 = lean_ctor_get(x_2, 5);
lean_dec(x_14);
lean_ctor_set(x_2, 5, x_8);
x_15 = lean_apply_2(x_1, x_2, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
x_20 = lean_ctor_get(x_2, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_21, 5, x_8);
x_22 = lean_apply_2(x_1, x_21, x_12);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_2);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
x_29 = lean_ctor_get(x_5, 2);
x_30 = lean_ctor_get(x_5, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_30, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_32);
lean_inc(x_2);
x_34 = l___private_Init_Lean_Elab_Command_3__setState(x_33, x_2, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 4);
lean_inc(x_40);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_41 = x_2;
} else {
 lean_dec_ref(x_2);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 6, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_40);
lean_ctor_set(x_42, 5, x_30);
x_43 = lean_apply_2(x_1, x_42, x_35);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_46 = x_34;
} else {
 lean_dec_ref(x_34);
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
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_4);
if (x_48 == 0)
{
return x_4;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_4);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3;
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
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(x_17, x_18, x_3);
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
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
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
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__9(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__14(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__14(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Elab_Command_addBuiltinCommandElab___spec__12(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__13(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__15(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__15(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_Elab_Command_addBuiltinCommandElab___spec__12(x_13, x_15);
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
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__15(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_Elab_Command_addBuiltinCommandElab___spec__12(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__15(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_PersistentHashMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__7(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_PersistentHashMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__7(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__11(x_13, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__11(x_15, x_2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
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
x_16 = l_Lean_SMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__6(x_12, x_1, x_3);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_Elab_Command_addBuiltinCommandElab___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Parser_registerParserAttribute___closed__5;
x_31 = lean_string_append(x_29, x_30);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(x_32, x_1);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_io_ref_get(x_5, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_io_ref_reset(x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_SMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__6(x_36, x_1, x_3);
x_41 = lean_io_ref_set(x_5, x_40, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_48 = x_35;
} else {
 lean_dec_ref(x_35);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_50 = l_Lean_Name_toString___closed__1;
x_51 = l_Lean_Name_toStringWithSep___main(x_50, x_1);
x_52 = l_Lean_Elab_Command_addBuiltinCommandElab___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_Parser_registerParserAttribute___closed__5;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_33);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
return x_6;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
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
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(x_1, x_6, x_7, x_4, x_5);
return x_8;
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_6);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_3);
x_28 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_Lean_initAttr;
x_35 = lean_box(0);
x_36 = l_Lean_ParametricAttribute_setParam___rarg(x_34, x_33, x_6, x_35);
x_37 = l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(x_36, x_4);
lean_dec(x_36);
return x_37;
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
lean_object* x_1; 
x_1 = lean_mk_string("unexpected command elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `CommandElab` expected");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4() {
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
x_6 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_23; 
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
x_23 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_ConstantInfo_type(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 4)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
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
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = l_Lean_nameToExprAux___main___closed__1;
x_38 = lean_string_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_1);
x_39 = lean_box(0);
x_14 = x_39;
goto block_22;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l___private_Init_Lean_Elab_Util_7__regTraceClasses___closed__1;
x_41 = lean_string_dec_eq(x_35, x_40);
lean_dec(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_1);
x_42 = lean_box(0);
x_14 = x_42;
goto block_22;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__1;
x_44 = lean_string_dec_eq(x_34, x_43);
lean_dec(x_34);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_1);
x_45 = lean_box(0);
x_14 = x_45;
goto block_22;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4;
x_47 = lean_string_dec_eq(x_33, x_46);
lean_dec(x_33);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_1);
x_48 = lean_box(0);
x_14 = x_48;
goto block_22;
}
else
{
lean_object* x_49; 
lean_dec(x_13);
x_49 = l_Lean_Elab_Command_declareBuiltinCommandElab(x_1, x_11, x_2, x_12);
return x_49;
}
}
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_50 = lean_box(0);
x_14 = x_50;
goto block_22;
}
}
else
{
lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_51 = lean_box(0);
x_14 = x_51;
goto block_22;
}
}
else
{
lean_object* x_52; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_52 = lean_box(0);
x_14 = x_52;
goto block_22;
}
}
else
{
lean_object* x_53; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_53 = lean_box(0);
x_14 = x_53;
goto block_22;
}
}
else
{
lean_object* x_54; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_54 = lean_box(0);
x_14 = x_54;
goto block_22;
}
}
else
{
lean_object* x_55; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_1);
x_55 = lean_box(0);
x_14 = x_55;
goto block_22;
}
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_2);
x_17 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_20 = lean_string_append(x_18, x_19);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_13;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
else
{
uint8_t x_56; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_10);
if (x_56 == 0)
{
return x_10;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_10, 0);
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_10);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin command elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2;
x_2 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5;
x_3 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__6;
x_4 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3;
x_5 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4;
x_6 = l_Lean_AttributeImpl_inhabited___closed__4;
x_7 = l_Lean_AttributeImpl_inhabited___closed__5;
x_8 = 1;
x_9 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_6);
lean_ctor_set(x_9, 6, x_7);
lean_ctor_set(x_9, 7, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*8, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
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
x_2 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4;
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
x_5 = l_Lean_Parser_mkCommandParserAttribute___closed__4;
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
x_1 = l_Lean_AttributeImpl_inhabited___closed__6;
x_2 = l_Lean_Elab_Command_commandElabAttribute___closed__4;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__6(x_2, x_7);
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
x_6 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_4, x_2);
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
x_9 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected command");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabCommand___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCommand___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_commandElabAttribute;
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_PersistentEnvExtension_getState___rarg(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_12, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_4);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Command_elabCommand___closed__6;
x_19 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_Term_elabTerm___closed__6;
x_21 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Command_throwError___rarg(x_1, x_21, x_2, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_apply_3(x_23, x_1, x_2, x_7);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Elab_Command_elabCommand___closed__3;
x_30 = l_Lean_Elab_Command_throwError___rarg(x_1, x_29, x_2, x_3);
return x_30;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_1, x_2);
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
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_3, 4, x_7);
x_8 = lean_apply_2(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_14);
x_17 = lean_apply_2(x_2, x_16, x_4);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_3, 4, x_7);
lean_inc(x_3);
x_8 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabCommand(x_9, x_3, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
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
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_21);
lean_inc(x_23);
x_24 = lean_apply_3(x_1, x_2, x_23, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Command_elabCommand(x_25, x_23, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_Command_8__mkTermContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(x_4);
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
x_11 = l_Lean_LocalContext_Inhabited___closed__2;
x_12 = l_Array_empty___closed__1;
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
x_19 = lean_ctor_get(x_5, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 4);
lean_inc(x_21);
lean_dec(x_5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_22 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_3);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
lean_ctor_set(x_22, 8, x_17);
lean_ctor_set(x_22, 9, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*10, x_7);
return x_22;
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_8__mkTermContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Command_8__mkTermContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Command_9__mkTermState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_MetavarContext_Inhabited___closed__1;
x_6 = l_Lean_Meta_MetaHasEval___rarg___closed__4;
x_7 = l_Lean_NameGenerator_Inhabited___closed__3;
x_8 = l_Lean_TraceState_Inhabited___closed__1;
x_9 = l_PersistentArray_empty___closed__3;
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_9);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_4);
return x_13;
}
}
lean_object* l___private_Init_Lean_Elab_Command_9__mkTermState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Command_9__mkTermState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_10__getVarDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(x_2);
x_4 = lean_ctor_get(x_3, 6);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Command_10__getVarDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Command_10__getVarDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Message_Inhabited;
x_2 = l_Lean_Elab_Command_State_inhabited;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 3);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 5);
lean_inc(x_13);
lean_dec(x_3);
lean_ctor_set(x_1, 3, x_13);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_2, 1, x_16);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_21 = x_1;
} else {
 lean_dec_ref(x_1);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_3, 5);
lean_inc(x_22);
lean_dec(x_3);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 4, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_27, 2);
lean_inc(x_32);
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_1, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_27, 5);
lean_inc(x_37);
lean_dec(x_27);
lean_ctor_set(x_1, 3, x_37);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_31);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_27, 5);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_47 = x_1;
} else {
 lean_dec_ref(x_1);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_41, 5);
lean_inc(x_48);
lean_dec(x_41);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 4, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg___closed__1;
x_52 = l_unreachable_x21___rarg(x_51);
return x_52;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_11__toCommandResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_11__toCommandResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_11__toCommandResult(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Message_Inhabited___closed__2;
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
x_8 = l___private_Init_Lean_Elab_Command_10__getVarDecls(x_6);
x_9 = l___private_Init_Lean_Elab_Command_8__mkTermContext(x_3, x_6, x_1);
x_10 = l___private_Init_Lean_Elab_Command_9__mkTermState(x_6);
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
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_13, 2);
lean_inc(x_19);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_19);
lean_ctor_set(x_16, 0, x_18);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_16, 2);
x_33 = lean_ctor_get(x_16, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
x_35 = l___private_Init_Lean_Elab_Command_3__setState(x_34, x_3, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
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
}
else
{
uint8_t x_43; 
lean_dec(x_13);
lean_dec(x_12);
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
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_11, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_3);
x_50 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_48, 2);
lean_inc(x_55);
lean_dec(x_48);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
lean_ctor_set(x_52, 1, x_55);
lean_ctor_set(x_52, 0, x_54);
x_59 = l___private_Init_Lean_Elab_Command_3__setState(x_52, x_3, x_53);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_49);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_49);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_52, 2);
x_69 = lean_ctor_get(x_52, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_69);
x_71 = l___private_Init_Lean_Elab_Command_3__setState(x_70, x_3, x_53);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
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
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_49);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_49);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_77 = x_71;
} else {
 lean_dec_ref(x_71);
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
uint8_t x_79; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_50);
if (x_79 == 0)
{
return x_50;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_50, 0);
x_81 = lean_ctor_get(x_50, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_50);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_11);
x_83 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_84 = l_unreachable_x21___rarg(x_83);
x_85 = lean_apply_2(x_84, x_3, x_7);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_5);
if (x_86 == 0)
{
return x_5;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_5, 0);
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_5);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_PersistentArray_push___rarg(x_11, x_5);
lean_ctor_set(x_8, 1, x_12);
x_13 = l___private_Init_Lean_Elab_Command_3__setState(x_8, x_2, x_9);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_28 = l_PersistentArray_push___rarg(x_25, x_5);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
return x_7;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_PersistentArray_push___rarg(x_15, x_9);
lean_ctor_set(x_12, 1, x_16);
x_17 = l___private_Init_Lean_Elab_Command_3__setState(x_12, x_2, x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
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
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
x_32 = lean_ctor_get(x_12, 2);
x_33 = lean_ctor_get(x_12, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_34 = l_PersistentArray_push___rarg(x_31, x_9);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
x_36 = l___private_Init_Lean_Elab_Command_3__setState(x_35, x_2, x_13);
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
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
 lean_ctor_set_tag(x_44, 0);
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_47);
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_22);
x_24 = l___private_Init_Lean_Elab_Command_3__setState(x_23, x_2, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
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
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(x_6);
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
x_11 = l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(x_10);
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
lean_object* l___private_Init_Lean_Elab_Command_12__addScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_3);
x_12 = l_Lean_Environment_registerNamespace___main(x_10, x_3);
x_13 = l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(x_11);
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
lean_ctor_set(x_7, 2, x_18);
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
lean_ctor_set(x_7, 2, x_35);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
x_47 = lean_ctor_get(x_7, 2);
x_48 = lean_ctor_get(x_7, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
lean_inc(x_3);
x_49 = l_Lean_Environment_registerNamespace___main(x_45, x_3);
x_50 = l_List_head_x21___at___private_Init_Lean_Elab_Command_8__mkTermContext___spec__1(x_47);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 6);
lean_inc(x_54);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 lean_ctor_release(x_50, 5);
 lean_ctor_release(x_50, 6);
 x_55 = x_50;
} else {
 lean_dec_ref(x_50);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 7, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_3);
lean_ctor_set(x_56, 4, x_52);
lean_ctor_set(x_56, 5, x_53);
lean_ctor_set(x_56, 6, x_54);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_48);
x_59 = l___private_Init_Lean_Elab_Command_3__setState(x_58, x_4, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_6);
if (x_68 == 0)
{
return x_6;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_6, 0);
x_70 = lean_ctor_get(x_6, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_6);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid scope");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___main(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
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
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_2, x_3, x_9, x_5, x_6);
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
x_16 = l___private_Init_Lean_Elab_Command_12__addScope(x_2, x_10, x_14, x_5, x_15);
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
x_22 = l___private_Init_Lean_Elab_Command_12__addScope(x_2, x_10, x_21, x_5, x_18);
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
x_31 = l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__3;
x_32 = l_Lean_Elab_Command_throwError___rarg(x_1, x_31, x_5, x_6);
return x_32;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Command_13__addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Elab_Command_13__addScopes(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Command_14__addNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_6 = 1;
x_7 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_7 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_6, x_2, x_3);
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
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_13 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_12, x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_getId(x_15);
lean_dec(x_15);
x_17 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_18 = 1;
x_19 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_17, x_18, x_16, x_2, x_3);
return x_19;
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
lean_object* _init_l_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Command_elabSection___closed__1;
x_7 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_6, x_2, x_3);
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
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_Command_elabSection___closed__1;
x_13 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_12, x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_elabSection___closed__1;
x_19 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_18, x_2, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Syntax_getArgs(x_15);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = lean_nat_dec_eq(x_21, x_14);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_15);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_21, x_23);
lean_dec(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Elab_Command_elabSection___closed__1;
x_26 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_25, x_2, x_3);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_1);
lean_inc(x_2);
x_27 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_31 = l_String_splitAux___main___closed__1;
x_32 = l___private_Init_Lean_Elab_Command_12__addScope(x_30, x_31, x_28, x_2, x_29);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_21);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_15, x_37);
lean_dec(x_15);
x_39 = l_Lean_Syntax_getKind___closed__4;
lean_inc(x_38);
x_40 = l_Lean_Syntax_isOfKind(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
x_41 = l_Lean_Elab_Command_elabSection___closed__1;
x_42 = l_Lean_Elab_Command_throwUnexpectedSyntax___rarg(x_1, x_41, x_2, x_3);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_43 = l_Lean_Syntax_getId(x_38);
lean_dec(x_38);
x_44 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_45 = 0;
x_46 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_44, x_45, x_43, x_2, x_3);
return x_46;
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
uint8_t l___private_Init_Lean_Elab_Command_15__checkAnonymousScope(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_Command_15__checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Command_15__checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Elab_Command_16__checkEndHeader___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Lean_Elab_Command_16__checkEndHeader___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_Command_16__checkEndHeader___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Elab_Command_16__checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Elab_Command_16__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_16__checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_Command_16__checkEndHeader(x_1, x_2);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_Elab_Command_getScopes(x_2, x_3);
x_6 = l_Lean_stxInh;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_4, x_7);
lean_dec(x_4);
x_9 = l_Lean_Syntax_getOptionalIdent_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_5, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_5, 1);
lean_inc(x_103);
lean_dec(x_5);
x_10 = x_7;
x_11 = x_102;
x_12 = x_103;
goto block_101;
}
else
{
uint8_t x_104; 
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_5);
if (x_104 == 0)
{
return x_5;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_5, 0);
x_106 = lean_ctor_get(x_5, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_5);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_9, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_5, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_5, 1);
lean_inc(x_110);
lean_dec(x_5);
x_111 = l_Lean_Name_getNumParts___main(x_108);
lean_dec(x_108);
x_10 = x_111;
x_11 = x_109;
x_12 = x_110;
goto block_101;
}
else
{
uint8_t x_112; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_5);
if (x_112 == 0)
{
return x_5;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_5, 0);
x_114 = lean_ctor_get(x_5, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_5);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
block_101:
{
lean_object* x_13; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_List_lengthAux___main___rarg(x_11, x_26);
x_28 = lean_nat_dec_lt(x_10, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_inc(x_2);
x_29 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_30, 2);
x_34 = l_List_lengthAux___main___rarg(x_33, x_26);
x_35 = lean_nat_sub(x_34, x_7);
lean_dec(x_34);
x_36 = l_List_drop___main___rarg(x_35, x_33);
lean_dec(x_33);
lean_ctor_set(x_30, 2, x_36);
lean_inc(x_2);
x_37 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_2, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Command_elabEnd___closed__9;
x_40 = l_Lean_Elab_Command_throwError___rarg(x_1, x_39, x_2, x_38);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_2);
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
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
x_51 = lean_ctor_get(x_30, 2);
x_52 = lean_ctor_get(x_30, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_53 = l_List_lengthAux___main___rarg(x_51, x_26);
x_54 = lean_nat_sub(x_53, x_7);
lean_dec(x_53);
x_55 = l_List_drop___main___rarg(x_54, x_51);
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_52);
lean_inc(x_2);
x_57 = l___private_Init_Lean_Elab_Command_3__setState(x_56, x_2, x_31);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Elab_Command_elabEnd___closed__9;
x_60 = l_Lean_Elab_Command_throwError___rarg(x_1, x_59, x_2, x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
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
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_2);
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
uint8_t x_69; 
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_29);
if (x_69 == 0)
{
return x_29;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_29, 0);
x_71 = lean_ctor_get(x_29, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_29);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_inc(x_2);
x_73 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_12);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 2);
x_78 = l_List_drop___main___rarg(x_10, x_77);
lean_dec(x_77);
lean_ctor_set(x_74, 2, x_78);
lean_inc(x_2);
x_79 = l___private_Init_Lean_Elab_Command_3__setState(x_74, x_2, x_75);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_13 = x_80;
goto block_25;
}
else
{
uint8_t x_81; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_79);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_74, 0);
x_86 = lean_ctor_get(x_74, 1);
x_87 = lean_ctor_get(x_74, 2);
x_88 = lean_ctor_get(x_74, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_74);
x_89 = l_List_drop___main___rarg(x_10, x_87);
lean_dec(x_87);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_88);
lean_inc(x_2);
x_91 = l___private_Init_Lean_Elab_Command_3__setState(x_90, x_2, x_75);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_13 = x_92;
goto block_25;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_73);
if (x_97 == 0)
{
return x_73;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_73, 0);
x_99 = lean_ctor_get(x_73, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_73);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
block_25:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_14; 
x_14 = l___private_Init_Lean_Elab_Command_15__checkAnonymousScope(x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_Command_elabEnd___closed__3;
x_16 = l_Lean_Elab_Command_throwError___rarg(x_1, x_15, x_2, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Init_Lean_Elab_Command_16__checkEndHeader___main(x_19, x_11);
lean_dec(x_11);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Command_elabEnd___closed__6;
x_22 = l_Lean_Elab_Command_throwError___rarg(x_1, x_21, x_2, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd), 3, 0);
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
x_8 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_6, x_7, x_2, x_4, x_5);
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
x_17 = lean_ctor_get(x_14, 2);
x_18 = l_Lean_Name_getNumParts___main(x_2);
lean_dec(x_2);
x_19 = l_List_drop___main___rarg(x_18, x_17);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
x_31 = lean_ctor_get(x_14, 2);
x_32 = lean_ctor_get(x_14, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_33 = l_Lean_Name_getNumParts___main(x_2);
lean_dec(x_2);
x_34 = l_List_drop___main___rarg(x_33, x_31);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_32);
x_36 = l___private_Init_Lean_Elab_Command_3__setState(x_35, x_4, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
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
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_13);
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
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_10);
if (x_48 == 0)
{
return x_10;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_5);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_5, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_6);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_apply_1(x_1, x_42);
lean_ctor_set(x_6, 0, x_43);
x_44 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_38);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_6, 0);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_6);
x_57 = lean_apply_1(x_1, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_5, 2, x_58);
x_59 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_38);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_5, 0);
x_69 = lean_ctor_get(x_5, 1);
x_70 = lean_ctor_get(x_5, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_5);
x_71 = lean_ctor_get(x_6, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_6, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_73 = x_6;
} else {
 lean_dec_ref(x_6);
 x_73 = lean_box(0);
}
x_74 = lean_apply_1(x_1, x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_70);
x_77 = l___private_Init_Lean_Elab_Command_3__setState(x_76, x_2, x_38);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
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
}
else
{
uint8_t x_86; 
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_4);
if (x_86 == 0)
{
return x_4;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_4, 0);
x_88 = lean_ctor_get(x_4, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_4);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
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
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
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
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_12 = lean_alloc_ctor(8, 2, 0);
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
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg), 4, 0);
return x_2;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_6, 1);
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 5);
lean_ctor_set(x_6, 1, x_46);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_38, 5, x_6);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_5, 2, x_47);
x_48 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_38, 0);
x_60 = lean_ctor_get(x_38, 1);
x_61 = lean_ctor_get(x_38, 2);
x_62 = lean_ctor_get(x_38, 3);
x_63 = lean_ctor_get(x_38, 4);
x_64 = lean_ctor_get(x_38, 5);
x_65 = lean_ctor_get(x_38, 6);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_38);
lean_ctor_set(x_6, 1, x_64);
lean_ctor_set(x_6, 0, x_1);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_63);
lean_ctor_set(x_66, 5, x_6);
lean_ctor_set(x_66, 6, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_5, 2, x_67);
x_68 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
lean_dec(x_6);
x_78 = lean_ctor_get(x_38, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_38, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_38, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_38, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_38, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_38, 6);
lean_inc(x_84);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_85 = x_38;
} else {
 lean_dec_ref(x_38);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 7, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_80);
lean_ctor_set(x_87, 3, x_81);
lean_ctor_set(x_87, 4, x_82);
lean_ctor_set(x_87, 5, x_86);
lean_ctor_set(x_87, 6, x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
lean_ctor_set(x_5, 2, x_88);
x_89 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
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
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = lean_ctor_get(x_5, 1);
x_100 = lean_ctor_get(x_5, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_5);
x_101 = lean_ctor_get(x_6, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_102 = x_6;
} else {
 lean_dec_ref(x_6);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_38, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_38, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_38, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_38, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_38, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_38, 5);
lean_inc(x_108);
x_109 = lean_ctor_get(x_38, 6);
lean_inc(x_109);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_110 = x_38;
} else {
 lean_dec_ref(x_38);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_102;
}
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_108);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 7, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_103);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_105);
lean_ctor_set(x_112, 3, x_106);
lean_ctor_set(x_112, 4, x_107);
lean_ctor_set(x_112, 5, x_111);
lean_ctor_set(x_112, 6, x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_101);
x_114 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_114, 0, x_98);
lean_ctor_set(x_114, 1, x_99);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_100);
x_115 = l___private_Init_Lean_Elab_Command_3__setState(x_114, x_2, x_39);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_122 = x_115;
} else {
 lean_dec_ref(x_115);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_4);
if (x_124 == 0)
{
return x_4;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_4, 0);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_4);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
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
x_8 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__4(x_4, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Elab_Command_addUnivLevel(x_7, x_2, x_3);
return x_8;
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
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Command_addUnivLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_box(0);
x_11 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_6, x_8, x_9, x_10, x_2, x_3);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot), 3, 0);
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
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_3, x_2, x_6, x_4, x_5);
lean_dec(x_6);
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
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_PersistentArray_push___rarg(x_14, x_8);
lean_ctor_set(x_11, 1, x_15);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_31 = l_PersistentArray_push___rarg(x_28, x_8);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
x_33 = l___private_Init_Lean_Elab_Command_3__setState(x_32, x_4, x_12);
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
lean_dec(x_8);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Command_throwError___spec__2(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(x_7, x_2, x_3, x_4, x_8);
return x_9;
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
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__8;
x_12 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 2;
x_14 = l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(x_1, x_13, x_12, x_3, x_4);
return x_14;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
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
lean_object* l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = 2;
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_throwError___spec__3(x_1, x_6, x_5, x_2, x_3);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* _init_l_Lean_Elab_Command_resolveNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown namespace '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_resolveNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_resolveNamespace___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_resolveNamespace___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_resolveNamespace___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_inc(x_2);
x_10 = l_Lean_Elab_Command_getOpenDecls(x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_1);
x_14 = l_Lean_Elab_resolveNamespace(x_5, x_8, x_12, x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Command_resolveNamespace___closed__3;
x_20 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__8;
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(x_22, x_2, x_13);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
lean_inc(x_1);
x_27 = l_Lean_Elab_resolveNamespace(x_5, x_8, x_25, x_1);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = l_Lean_Name_toString___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_1);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_Elab_Command_resolveNamespace___closed__3;
x_33 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Term_throwUnexpectedSyntax___rarg___closed__8;
x_35 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(x_35, x_2, x_26);
lean_dec(x_2);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
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
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
return x_4;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
x_7 = l_Lean_addAlias(x_1, x_5, x_6);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(1u);
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
x_12 = l_Lean_Elab_Command_getCurrNamespace(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_72; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_72 = lean_name_eq(x_10, x_13);
if (x_72 == 0)
{
lean_dec(x_1);
x_15 = x_14;
goto block_71;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
x_73 = l_Lean_Elab_Command_elabExport___closed__3;
x_74 = l_Lean_Elab_Command_throwError___rarg(x_1, x_73, x_2, x_14);
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
block_71:
{
lean_object* x_16; 
lean_inc(x_2);
x_16 = l_Lean_Elab_Command_getEnv(x_2, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_array_get(x_5, x_4, x_20);
x_22 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_24 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(x_4, x_10, x_13, x_17, x_22, x_23, x_19, x_2, x_18);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_2);
x_27 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_31, x_25);
lean_ctor_set(x_28, 0, x_32);
x_33 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_29);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
x_46 = lean_ctor_get(x_28, 2);
x_47 = lean_ctor_get(x_28, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_48 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_44, x_25);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
x_50 = l___private_Init_Lean_Elab_Command_3__setState(x_49, x_2, x_29);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
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
else
{
uint8_t x_59; 
lean_dec(x_25);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_27);
if (x_59 == 0)
{
return x_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
return x_24;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_24, 0);
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_24);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
return x_16;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_16);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_12);
if (x_79 == 0)
{
return x_12;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_12, 0);
x_81 = lean_ctor_get(x_12, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_12);
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
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_9);
if (x_83 == 0)
{
return x_9;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_9, 0);
x_85 = lean_ctor_get(x_9, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_9);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabExport), 3, 0);
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_6, 1);
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 4);
lean_ctor_set(x_6, 1, x_46);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_38, 4, x_6);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_5, 2, x_47);
x_48 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_38, 0);
x_60 = lean_ctor_get(x_38, 1);
x_61 = lean_ctor_get(x_38, 2);
x_62 = lean_ctor_get(x_38, 3);
x_63 = lean_ctor_get(x_38, 4);
x_64 = lean_ctor_get(x_38, 5);
x_65 = lean_ctor_get(x_38, 6);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_38);
lean_ctor_set(x_6, 1, x_63);
lean_ctor_set(x_6, 0, x_1);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_6);
lean_ctor_set(x_66, 5, x_64);
lean_ctor_set(x_66, 6, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_5, 2, x_67);
x_68 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
lean_dec(x_6);
x_78 = lean_ctor_get(x_38, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_38, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_38, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_38, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_38, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_38, 6);
lean_inc(x_84);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_85 = x_38;
} else {
 lean_dec_ref(x_38);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_82);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 7, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_80);
lean_ctor_set(x_87, 3, x_81);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_87, 5, x_83);
lean_ctor_set(x_87, 6, x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_77);
lean_ctor_set(x_5, 2, x_88);
x_89 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
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
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = lean_ctor_get(x_5, 1);
x_100 = lean_ctor_get(x_5, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_5);
x_101 = lean_ctor_get(x_6, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_102 = x_6;
} else {
 lean_dec_ref(x_6);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_38, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_38, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_38, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_38, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_38, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_38, 5);
lean_inc(x_108);
x_109 = lean_ctor_get(x_38, 6);
lean_inc(x_109);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_110 = x_38;
} else {
 lean_dec_ref(x_38);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_102;
}
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_107);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 7, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_103);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_105);
lean_ctor_set(x_112, 3, x_106);
lean_ctor_set(x_112, 4, x_111);
lean_ctor_set(x_112, 5, x_108);
lean_ctor_set(x_112, 6, x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_101);
x_114 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_114, 0, x_98);
lean_ctor_set(x_114, 1, x_99);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_100);
x_115 = l___private_Init_Lean_Elab_Command_3__setState(x_114, x_2, x_39);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_122 = x_115;
} else {
 lean_dec_ref(x_115);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_4);
if (x_124 == 0)
{
return x_4;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_4, 0);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_4);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
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
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
x_11 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
lean_inc(x_5);
x_12 = l_Lean_Elab_Command_resolveNamespace(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_5);
x_17 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_16, x_5, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_18;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
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
lean_dec(x_5);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_box(0);
x_11 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_9, x_8, x_6, x_10, x_2, x_3);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = l_Lean_Syntax_getId(x_11);
lean_inc(x_12);
x_13 = l_Lean_Name_append___main(x_1, x_12);
lean_inc(x_6);
x_14 = l_Lean_Elab_Command_getEnv(x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Environment_contains(x_15, x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_inc(x_6);
x_18 = l_Lean_Elab_Command_logUnknownDecl(x_11, x_13, x_6, x_16);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_21;
x_5 = x_19;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_4);
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
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_13);
lean_inc(x_6);
x_28 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_27, x_6, x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_31;
x_5 = x_29;
x_7 = x_30;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
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
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_box(0);
x_17 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_10, x_15, x_14, x_6, x_16, x_2, x_11);
lean_dec(x_14);
lean_dec(x_10);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = l_Lean_Syntax_getId(x_12);
lean_inc(x_13);
x_14 = l_Lean_Name_append___main(x_1, x_13);
lean_inc(x_2);
x_15 = l_Lean_Environment_contains(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_inc(x_7);
x_16 = l_Lean_Elab_Command_logUnknownDecl(x_12, x_14, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_18;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_25;
x_6 = x_24;
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
x_5 = l_Lean_stxInh;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
x_19 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_20 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_10, x_13, x_19, x_18, x_6, x_17, x_2, x_14);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_23, x_2, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_2);
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
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
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
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_5 = l_Lean_stxInh;
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
x_16 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_10, x_12, x_14, x_6, x_15, x_2, x_11);
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
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_asNode(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_13 = lean_name_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_15 = lean_name_eq(x_9, x_14);
lean_dec(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabOpenRenaming(x_8, x_2, x_3);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Command_elabOpenHiding(x_8, x_2, x_3);
lean_dec(x_8);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = l_Lean_Elab_Command_elabOpenOnly(x_8, x_2, x_3);
lean_dec(x_8);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_9);
x_19 = l_Lean_Elab_Command_elabOpenSimple(x_8, x_2, x_3);
lean_dec(x_8);
return x_19;
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
lean_object* l_Lean_Elab_Command_elabMixfix___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabMixfix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMixfix___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabMixfix___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_elabMixfix(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabMixfix");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMixfix___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabReserve___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabReserve(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReserve___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabReserve___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_elabReserve(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabReserve");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReserve___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_reserve___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabNotation___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabNotation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_elabNotation(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNotation");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNotation___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_notation___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__3;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 6);
x_46 = lean_array_push(x_45, x_1);
lean_ctor_set(x_38, 6, x_46);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
x_60 = lean_ctor_get(x_38, 2);
x_61 = lean_ctor_get(x_38, 3);
x_62 = lean_ctor_get(x_38, 4);
x_63 = lean_ctor_get(x_38, 5);
x_64 = lean_ctor_get(x_38, 6);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_65 = lean_array_push(x_64, x_1);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_59);
lean_ctor_set(x_66, 2, x_60);
lean_ctor_set(x_66, 3, x_61);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_63);
lean_ctor_set(x_66, 6, x_65);
lean_ctor_set(x_6, 0, x_66);
x_67 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_6, 1);
lean_inc(x_76);
lean_dec(x_6);
x_77 = lean_ctor_get(x_38, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_38, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_38, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_38, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_38, 6);
lean_inc(x_83);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_84 = x_38;
} else {
 lean_dec_ref(x_38);
 x_84 = lean_box(0);
}
x_85 = lean_array_push(x_83, x_1);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 7, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set(x_86, 2, x_79);
lean_ctor_set(x_86, 3, x_80);
lean_ctor_set(x_86, 4, x_81);
lean_ctor_set(x_86, 5, x_82);
lean_ctor_set(x_86, 6, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
lean_ctor_set(x_5, 2, x_87);
x_88 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_97 = lean_ctor_get(x_5, 0);
x_98 = lean_ctor_get(x_5, 1);
x_99 = lean_ctor_get(x_5, 3);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_5);
x_100 = lean_ctor_get(x_6, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_101 = x_6;
} else {
 lean_dec_ref(x_6);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_38, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_38, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_38, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_38, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_38, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_38, 5);
lean_inc(x_107);
x_108 = lean_ctor_get(x_38, 6);
lean_inc(x_108);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_109 = x_38;
} else {
 lean_dec_ref(x_38);
 x_109 = lean_box(0);
}
x_110 = lean_array_push(x_108, x_1);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 7, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_103);
lean_ctor_set(x_111, 2, x_104);
lean_ctor_set(x_111, 3, x_105);
lean_ctor_set(x_111, 4, x_106);
lean_ctor_set(x_111, 5, x_107);
lean_ctor_set(x_111, 6, x_110);
if (lean_is_scalar(x_101)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_101;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_100);
x_113 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_113, 0, x_97);
lean_ctor_set(x_113, 1, x_98);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_99);
x_114 = l___private_Init_Lean_Elab_Command_3__setState(x_113, x_2, x_39);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_121 = x_114;
} else {
 lean_dec_ref(x_114);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_4);
if (x_123 == 0)
{
return x_4;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_4, 0);
x_125 = lean_ctor_get(x_4, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_4);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_mkOptionalNode___closed__1;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_stxInh;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_4, x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__1___boxed), 4, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l___private_Init_Lean_Elab_Command_10__getVarDecls(x_7);
x_14 = l___private_Init_Lean_Elab_Command_8__mkTermContext(x_2, x_7, x_5);
x_15 = l___private_Init_Lean_Elab_Command_9__mkTermState(x_7);
lean_dec(x_7);
x_16 = l_Lean_Elab_Term_elabBinders___rarg(x_13, x_12, x_14, x_15);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_2);
x_18 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
lean_ctor_set(x_20, 1, x_23);
lean_ctor_set(x_20, 0, x_22);
lean_inc(x_2);
x_27 = l___private_Init_Lean_Elab_Command_3__setState(x_20, x_2, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_11, x_2, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
lean_inc(x_2);
x_37 = l___private_Init_Lean_Elab_Command_3__setState(x_36, x_2, x_21);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_11, x_2, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
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
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
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
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_11);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_2);
x_51 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_8);
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
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_49, 2);
lean_inc(x_56);
lean_dec(x_49);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_53, 0);
lean_dec(x_59);
lean_ctor_set(x_53, 1, x_56);
lean_ctor_set(x_53, 0, x_55);
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
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_53);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_56);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
x_72 = l___private_Init_Lean_Elab_Command_3__setState(x_71, x_2, x_54);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
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
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_50);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
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
uint8_t x_80; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_51);
if (x_80 == 0)
{
return x_51;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_51, 0);
x_82 = lean_ctor_get(x_51, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_51);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_16);
x_84 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_85 = l_unreachable_x21___rarg(x_84);
lean_inc(x_2);
x_86 = lean_apply_2(x_85, x_2, x_8);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_11, x_2, x_87);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_6);
if (x_93 == 0)
{
return x_6;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_6, 0);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_6);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_38, 6);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_46, x_45);
lean_ctor_set(x_38, 6, x_47);
x_48 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_ctor_get(x_38, 0);
x_60 = lean_ctor_get(x_38, 1);
x_61 = lean_ctor_get(x_38, 2);
x_62 = lean_ctor_get(x_38, 3);
x_63 = lean_ctor_get(x_38, 4);
x_64 = lean_ctor_get(x_38, 5);
x_65 = lean_ctor_get(x_38, 6);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_38);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_66, x_65);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_62);
lean_ctor_set(x_68, 4, x_63);
lean_ctor_set(x_68, 5, x_64);
lean_ctor_set(x_68, 6, x_67);
lean_ctor_set(x_6, 0, x_68);
x_69 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_6, 1);
lean_inc(x_78);
lean_dec(x_6);
x_79 = lean_ctor_get(x_38, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_38, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_38, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_38, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_38, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_38, 6);
lean_inc(x_85);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_86 = x_38;
} else {
 lean_dec_ref(x_38);
 x_86 = lean_box(0);
}
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_87, x_85);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 7, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_81);
lean_ctor_set(x_89, 3, x_82);
lean_ctor_set(x_89, 4, x_83);
lean_ctor_set(x_89, 5, x_84);
lean_ctor_set(x_89, 6, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
lean_ctor_set(x_5, 2, x_90);
x_91 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_100 = lean_ctor_get(x_5, 0);
x_101 = lean_ctor_get(x_5, 1);
x_102 = lean_ctor_get(x_5, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_5);
x_103 = lean_ctor_get(x_6, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_104 = x_6;
} else {
 lean_dec_ref(x_6);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_38, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_38, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_38, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_38, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_38, 4);
lean_inc(x_109);
x_110 = lean_ctor_get(x_38, 5);
lean_inc(x_110);
x_111 = lean_ctor_get(x_38, 6);
lean_inc(x_111);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_112 = x_38;
} else {
 lean_dec_ref(x_38);
 x_112 = lean_box(0);
}
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_113, x_111);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 7, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_106);
lean_ctor_set(x_115, 2, x_107);
lean_ctor_set(x_115, 3, x_108);
lean_ctor_set(x_115, 4, x_109);
lean_ctor_set(x_115, 5, x_110);
lean_ctor_set(x_115, 6, x_114);
if (lean_is_scalar(x_104)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_104;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_103);
x_117 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_117, 0, x_100);
lean_ctor_set(x_117, 1, x_101);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_102);
x_118 = l___private_Init_Lean_Elab_Command_3__setState(x_117, x_2, x_39);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_stxInh;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_4, x_10);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___lambda__1___boxed), 4, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l___private_Init_Lean_Elab_Command_10__getVarDecls(x_7);
x_15 = l___private_Init_Lean_Elab_Command_8__mkTermContext(x_2, x_7, x_5);
x_16 = l___private_Init_Lean_Elab_Command_9__mkTermState(x_7);
lean_dec(x_7);
x_17 = l_Lean_Elab_Term_elabBinders___rarg(x_14, x_13, x_15, x_16);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_2);
x_19 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_18, 2);
lean_inc(x_24);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
lean_ctor_set(x_21, 1, x_24);
lean_ctor_set(x_21, 0, x_23);
lean_inc(x_2);
x_28 = l___private_Init_Lean_Elab_Command_3__setState(x_21, x_2, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_12, x_2, x_29);
lean_dec(x_12);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_21, 2);
x_36 = lean_ctor_get(x_21, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
lean_inc(x_2);
x_38 = l___private_Init_Lean_Elab_Command_3__setState(x_37, x_2, x_22);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_12, x_2, x_39);
lean_dec(x_12);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
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
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_19);
if (x_45 == 0)
{
return x_19;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
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
x_49 = lean_ctor_get(x_17, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_dec(x_17);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_2);
x_52 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_8);
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
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_ctor_get(x_50, 2);
lean_inc(x_57);
lean_dec(x_50);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
lean_ctor_set(x_54, 1, x_57);
lean_ctor_set(x_54, 0, x_56);
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
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_54, 2);
x_71 = lean_ctor_get(x_54, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_56);
lean_ctor_set(x_72, 1, x_57);
lean_ctor_set(x_72, 2, x_70);
lean_ctor_set(x_72, 3, x_71);
x_73 = l___private_Init_Lean_Elab_Command_3__setState(x_72, x_2, x_55);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_51);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_51);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_52);
if (x_81 == 0)
{
return x_52;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_52, 0);
x_83 = lean_ctor_get(x_52, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_52);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_17);
x_85 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_86 = l_unreachable_x21___rarg(x_85);
lean_inc(x_2);
x_87 = lean_apply_2(x_86, x_2, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_12, x_2, x_88);
lean_dec(x_12);
return x_89;
}
else
{
uint8_t x_90; 
lean_dec(x_12);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_6);
if (x_94 == 0)
{
return x_6;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_6, 0);
x_96 = lean_ctor_get(x_6, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_6);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
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
x_8 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_7, x_7, x_5, x_6);
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
x_13 = l___private_Init_Lean_Elab_Term_19__synthesizeSyntheticMVarsAux___main(x_11, x_12, x_5, x_10);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
x_18 = l_Lean_Elab_Term_instantiateMVars(x_3, x_9, x_5, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_instantiateMVars(x_3, x_16, x_5, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__7;
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_28 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = 0;
x_30 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_3, x_29, x_28, x_5, x_23);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_12);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_5);
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
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
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
lean_dec(x_5);
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
lean_object* l_Lean_Elab_Command_elabCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_stxInh;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_4, x_10);
lean_dec(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___lambda__1___boxed), 6, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_1);
x_13 = l___private_Init_Lean_Elab_Command_10__getVarDecls(x_7);
x_14 = l___private_Init_Lean_Elab_Command_8__mkTermContext(x_2, x_7, x_5);
x_15 = l___private_Init_Lean_Elab_Command_9__mkTermState(x_7);
lean_dec(x_7);
x_16 = l_Lean_Elab_Term_elabBinders___rarg(x_13, x_12, x_14, x_15);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_2);
x_19 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_18, 2);
lean_inc(x_24);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
lean_ctor_set(x_21, 1, x_24);
lean_ctor_set(x_21, 0, x_23);
x_28 = l___private_Init_Lean_Elab_Command_3__setState(x_21, x_2, x_22);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_17);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_21, 2);
x_38 = lean_ctor_get(x_21, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
x_40 = l___private_Init_Lean_Elab_Command_3__setState(x_39, x_2, x_22);
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
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_17);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
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
x_52 = lean_ctor_get(x_16, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_16, 1);
lean_inc(x_53);
lean_dec(x_16);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_2);
x_55 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_8);
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
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_53, 2);
lean_inc(x_60);
lean_dec(x_53);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
lean_ctor_set(x_57, 1, x_60);
lean_ctor_set(x_57, 0, x_59);
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_57, 2);
x_74 = lean_ctor_get(x_57, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_57);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_59);
lean_ctor_set(x_75, 1, x_60);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_74);
x_76 = l___private_Init_Lean_Elab_Command_3__setState(x_75, x_2, x_58);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
 lean_ctor_set_tag(x_79, 1);
}
lean_ctor_set(x_79, 0, x_54);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_54);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_55);
if (x_84 == 0)
{
return x_55;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_55, 0);
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_55);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_16);
x_88 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_89 = l_unreachable_x21___rarg(x_88);
x_90 = lean_apply_2(x_89, x_2, x_8);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
return x_6;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_6, 0);
x_93 = lean_ctor_get(x_6, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_6);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
x_6 = lean_ctor_get(x_5, 2);
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
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
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
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
x_14 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__4(x_13, x_4);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_97; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_97 = l_Lean_Syntax_isNone(x_8);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_99 = l_Lean_Syntax_getArgs(x_98);
lean_dec(x_98);
x_100 = lean_unsigned_to_nat(2u);
x_101 = l_Array_empty___closed__1;
x_102 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_100, x_99, x_5, x_101);
lean_dec(x_99);
lean_inc(x_3);
lean_inc(x_10);
x_103 = l_Array_iterateMAux___main___at_Lean_Elab_Command_withDeclId___spec__5(x_1, x_102, x_5, x_10, x_3, x_11);
lean_dec(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_12 = x_104;
x_13 = x_105;
goto block_96;
}
else
{
uint8_t x_106; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_8);
lean_inc(x_10);
x_12 = x_10;
x_13 = x_11;
goto block_96;
}
block_96:
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_17 = 1;
lean_inc(x_3);
lean_inc(x_14);
x_18 = l___private_Init_Lean_Elab_Command_13__addScopes___main(x_1, x_16, x_17, x_14, x_3, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_3);
x_20 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__1(x_12, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_name_mk_string(x_22, x_15);
lean_inc(x_3);
x_24 = lean_apply_3(x_2, x_23, x_3, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_3);
lean_inc(x_10);
x_27 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__2(x_10, x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_3);
x_29 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 2);
x_34 = l_Lean_Name_getNumParts___main(x_14);
lean_dec(x_14);
x_35 = l_List_drop___main___rarg(x_34, x_33);
lean_dec(x_33);
lean_ctor_set(x_30, 2, x_35);
x_36 = l___private_Init_Lean_Elab_Command_3__setState(x_30, x_3, x_31);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_25);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_25);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
x_47 = lean_ctor_get(x_30, 2);
x_48 = lean_ctor_get(x_30, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_49 = l_Lean_Name_getNumParts___main(x_14);
lean_dec(x_14);
x_50 = l_List_drop___main___rarg(x_49, x_47);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_48);
x_52 = l___private_Init_Lean_Elab_Command_3__setState(x_51, x_3, x_31);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
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
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_25);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_25);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_29);
if (x_60 == 0)
{
return x_29;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_29, 0);
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_29);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_25);
lean_dec(x_14);
x_64 = lean_ctor_get(x_27, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_27, 1);
lean_inc(x_65);
lean_dec(x_27);
x_66 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__3(x_10, x_3, x_65);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_64);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_66);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_14);
x_75 = lean_ctor_get(x_24, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_24, 1);
lean_inc(x_76);
lean_dec(x_24);
x_77 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_withDeclId___spec__4(x_10, x_3, x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
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
else
{
uint8_t x_82; 
lean_dec(x_75);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_20);
if (x_86 == 0)
{
return x_20;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_20, 0);
x_88 = lean_ctor_get(x_20, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_18);
if (x_90 == 0)
{
return x_18;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_18, 0);
x_92 = lean_ctor_get(x_18, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_18);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_94 = l_Lean_Elab_Command_withDeclId___closed__3;
x_95 = l_Lean_Elab_Command_throwError___rarg(x_1, x_94, x_3, x_13);
return x_95;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_9);
if (x_110 == 0)
{
return x_9;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_9, 0);
x_112 = lean_ctor_get(x_9, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_9);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
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
x_9 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__4(x_8, x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
lean_inc(x_3);
x_20 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_19);
x_25 = l___private_Init_Lean_Elab_Command_3__setState(x_21, x_3, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
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
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_21, 1);
x_37 = lean_ctor_get(x_21, 2);
x_38 = lean_ctor_get(x_21, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
x_40 = l___private_Init_Lean_Elab_Command_3__setState(x_39, x_3, x_22);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
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
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_19);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
return x_5;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_5, 0);
x_55 = lean_ctor_get(x_5, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_5);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
return x_5;
}
}
lean_object* initialize_Init_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object*);
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_TermBinders(lean_object*);
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
l_Lean_Elab_Command_CommandElabM_monadLog = _init_l_Lean_Elab_Command_CommandElabM_monadLog();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_monadLog);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__1);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__2);
l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3 = _init_l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_MonadQuotation___closed__3);
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
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__6 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__6);
l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__7 = _init_l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__7);
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
l_Lean_Elab_Command_elabCommand___closed__1 = _init_l_Lean_Elab_Command_elabCommand___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___closed__1);
l_Lean_Elab_Command_elabCommand___closed__2 = _init_l_Lean_Elab_Command_elabCommand___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___closed__2);
l_Lean_Elab_Command_elabCommand___closed__3 = _init_l_Lean_Elab_Command_elabCommand___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___closed__3);
l_Lean_Elab_Command_elabCommand___closed__4 = _init_l_Lean_Elab_Command_elabCommand___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___closed__4);
l_Lean_Elab_Command_elabCommand___closed__5 = _init_l_Lean_Elab_Command_elabCommand___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___closed__5);
l_Lean_Elab_Command_elabCommand___closed__6 = _init_l_Lean_Elab_Command_elabCommand___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabCommand___closed__6);
l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_11__toCommandResult___rarg___closed__1);
l_Lean_Elab_Command_CommandElabM_inhabited___closed__1 = _init_l_Lean_Elab_Command_CommandElabM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CommandElabM_inhabited___closed__1);
l_Lean_Elab_Command_runTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Command_runTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_runTermElabM___rarg___closed__1);
l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__1 = _init_l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__1);
l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__2 = _init_l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__2);
l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__3 = _init_l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_13__addScopes___main___closed__3);
l_Lean_Elab_Command_elabNamespace___closed__1 = _init_l_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabNamespace___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSection___closed__1 = _init_l_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSection___closed__1);
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
l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__6 = _init_l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__6);
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
l_Lean_Elab_Command_resolveNamespace___closed__1 = _init_l_Lean_Elab_Command_resolveNamespace___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_resolveNamespace___closed__1);
l_Lean_Elab_Command_resolveNamespace___closed__2 = _init_l_Lean_Elab_Command_resolveNamespace___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_resolveNamespace___closed__2);
l_Lean_Elab_Command_resolveNamespace___closed__3 = _init_l_Lean_Elab_Command_resolveNamespace___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_resolveNamespace___closed__3);
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
l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation(lean_io_mk_world());
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
