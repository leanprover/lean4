// Lean compiler output
// Module: Init.Lean.Elab.Command
// Imports: Init.Lean.Elab.Alias Init.Lean.Elab.Log Init.Lean.Elab.ResolveName Init.Lean.Elab.Term
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
extern lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2___closed__1;
uint8_t l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Command_getUniverseNames___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_addUniverse___closed__4;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__4;
lean_object* l_Lean_Elab_Command_elabSection(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace(lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Init_Lean_Elab_Command_5__addScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addUniverse___closed__1;
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__3;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes___main(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Command_mkCommandElabAttribute___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_check___closed__1;
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_Elab_Command_elabCommand___closed__4;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3;
lean_object* l_Lean_Elab_Command_getUniverseNames(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3;
lean_object* l_Lean_Elab_Command_addUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2;
extern lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__3;
lean_object* l_unreachable_x21___rarg(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Command_mkCommandElabAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__1;
lean_object* l_Lean_Environment_registerNamespace___main(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable(lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_4__toCommandResult(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addUniverse___closed__2;
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_7__checkAnonymousScope(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__10(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__1;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_getOpenDecls___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__2;
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_stxInh;
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Elab_Command_3__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabEnd___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__2;
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_elabCommand___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getUniverseNames___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__2;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse(lean_object*);
extern lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__5;
lean_object* l_Lean_Elab_Command_setEnv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr(lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNotation___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addAlias(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport(lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Command_mkCommandElabAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__10___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_inhabited;
extern lean_object* l_Lean_Meta_MetaHasEval___rarg___closed__4;
extern lean_object* l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables(lean_object*);
lean_object* l_Lean_Elab_Command_elabMixfix___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUniverse___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__9;
lean_object* l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__3;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd___closed__4;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__1;
lean_object* l_Lean_Elab_Command_resolveNamespace___closed__2;
lean_object* l_Lean_Elab_Command_elabNotation___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__4;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__6;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_Command_resolveNamespace___closed__1;
lean_object* l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkBuiltinCommandElabTable(lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getOpenDecls___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__6;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__3;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
lean_object* l_Lean_Elab_Command_addUniverse___closed__6;
lean_object* l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMixfix___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
lean_object* l_Lean_Elab_Command_getCurrNamespace(lean_object*);
extern lean_object* l_List_Monad;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___rarg(lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__2;
extern lean_object* l_Lean_Elab_Term_elabTerm___closed__6;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__2;
lean_object* l_Lean_Elab_Command_elabExport___closed__3;
extern lean_object* l_Lean_Parser_mkCommandParserAttribute___closed__4;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_dbgTrace(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__8;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
lean_object* l___private_Init_Lean_Elab_Command_3__getVarDecls___boxed(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__3;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__5;
lean_object* l_mkHashMap___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__2(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrNamespace___boxed(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__2;
extern lean_object* l_Lean_Parser_Command_docComment___elambda__1___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__3;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__3;
lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariables___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__4;
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab___closed__1;
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Message_Inhabited;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_1__mkTermContext___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at___private_Init_Lean_Elab_Term_17__reportStuckSyntheticMVars___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__7(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses(lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg___closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScopes(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverses___closed__2;
extern lean_object* l_Lean_Parser_Command_docComment___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabExport(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_builtinCommandElabTable;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_ReaderT_read___at_Lean_Elab_Command_CommandElabM_monadLog___spec__1(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__7___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__10(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__2;
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Elab_Command_Scope_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__7;
lean_object* l___private_Init_Lean_Elab_Command_7__checkAnonymousScope___boxed(lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck(lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_8__checkEndHeader___main(lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5(lean_object*, size_t, lean_object*);
uint8_t l___private_Init_Lean_Elab_Command_8__checkEndHeader(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__6;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__3;
extern lean_object* l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_notation___elambda__1___closed__2;
size_t l_USize_land(size_t, size_t);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_18__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrNamespace___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__3;
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__8;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__6;
lean_object* l___private_Init_Lean_Elab_Command_8__checkEndHeader___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_Elab_Command_getEnv___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_addUniverse___closed__5;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addUniverse___closed__3;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__2;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_AssocList_contains___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReserve(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__1;
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__2;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__1;
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_getScope(lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__6;
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
lean_object* l_AssocList_foldlM___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__14(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_5__addScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_reserve___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_8__checkEndHeader___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabReserve___closed__3;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__5;
lean_object* l_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__2;
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___closed__3;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__2;
extern lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute___closed__2;
lean_object* l_Lean_SMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReserve___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_2__mkTermState___boxed(lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveNamespace___closed__3;
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes___main___closed__1;
lean_object* l_Lean_Elab_Command_getEnv___rarg(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNotation(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__1;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Command_State_inhabited;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabMixfix___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getOpenDecls(lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__2;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3;
lean_object* l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_getEnv(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabUniverse___closed__1;
lean_object* l___private_Init_Lean_Elab_Command_4__toCommandResult___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___closed__3;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_Elab_Command_addBuiltinCommandElab___spec__12(lean_object*, lean_object*);
extern lean_object* l_PUnit_Inhabited;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__4;
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__7;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_Elab_Command_setEnv(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3;
extern lean_object* l_Lean_Parser_Command_variables___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Command_2__mkTermState(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Lean_Elab_Command_elabReserve___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__2;
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__10;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3;
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_1__mkTermContext(lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMixfix(lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNotation___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabVariable___closed__1;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute___closed__1;
lean_object* l_Lean_Elab_Command_getScopes___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
lean_object* l_Lean_Elab_Command_elabEnd___closed__7;
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand___closed__3;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__1;
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_Elab_Command_addBuiltinCommandElab___spec__11(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
extern lean_object* l_Lean_initAttr;
extern lean_object* l_EStateM_MonadState___closed__2;
lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__2;
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_addUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___closed__5;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabEnd___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1___boxed(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = lean_box(0);
x_2 = l_Lean_EnvExtension_setState___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_Command_State_inhabited___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
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
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_10);
return x_12;
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
lean_object* l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_3, 1, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__2___boxed), 3, 0);
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__3___boxed), 3, 0);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_MonadState___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__6;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__7;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_CommandElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_CommandElabM_monadLog___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__9;
x_2 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__3;
x_3 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__5;
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
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
lean_object* l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_lift___at_Lean_Elab_Command_CommandElabM_monadLog___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_CommandElabM_monadLog___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
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
lean_object* x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Command_addBuiltinCommandElab___spec__5(x_13, x_14, x_3);
lean_dec(x_13);
return x_15;
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
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(x_17, x_18, x_3);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
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
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(x_4, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__4(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_HashMapImp_contains___at_Lean_Elab_Command_addBuiltinCommandElab___spec__2(x_9, x_2);
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
lean_dec(x_8);
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
x_30 = l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
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
lean_dec(x_32);
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
x_54 = l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
x_2 = l_Lean_Parser_Command_docComment___elambda__1___closed__1;
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
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_Command_docComment___elambda__1___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_8, x_3, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
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
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_nameToExprAux___main___closed__1;
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_38 = lean_box(0);
x_13 = x_38;
goto block_21;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
x_40 = lean_string_dec_eq(x_34, x_39);
lean_dec(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_41 = lean_box(0);
x_13 = x_41;
goto block_21;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Parser_Command_docComment___elambda__1___closed__1;
x_43 = lean_string_dec_eq(x_33, x_42);
lean_dec(x_33);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_44 = lean_box(0);
x_13 = x_44;
goto block_21;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__4;
x_46 = lean_string_dec_eq(x_32, x_45);
lean_dec(x_32);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_10);
lean_dec(x_1);
x_47 = lean_box(0);
x_13 = x_47;
goto block_21;
}
else
{
lean_object* x_48; 
lean_dec(x_12);
x_48 = l_Lean_Elab_Command_declareBuiltinCommandElab(x_1, x_10, x_2, x_11);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_49 = lean_box(0);
x_13 = x_49;
goto block_21;
}
}
else
{
lean_object* x_50; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_50 = lean_box(0);
x_13 = x_50;
goto block_21;
}
}
else
{
lean_object* x_51; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_51 = lean_box(0);
x_13 = x_51;
goto block_21;
}
}
else
{
lean_object* x_52; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_52 = lean_box(0);
x_13 = x_52;
goto block_21;
}
}
else
{
lean_object* x_53; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_53 = lean_box(0);
x_13 = x_53;
goto block_21;
}
}
else
{
lean_object* x_54; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_1);
x_54 = lean_box(0);
x_13 = x_54;
goto block_21;
}
}
block_21:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_2);
x_16 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_registerBuiltinCommandElabAttr___lambda__1___closed__3;
x_19 = lean_string_append(x_17, x_18);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_12;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Command_mkCommandElabAttribute___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
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
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_HashMap_Inhabited___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Command_mkBuiltinCommandElabTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__2;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_get(x_13, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_19);
x_26 = x_19;
x_27 = lean_array_push(x_21, x_26);
x_28 = lean_io_ref_set(x_13, x_27, x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_19);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
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
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_19);
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
else
{
uint8_t x_41; 
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
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
lean_dec(x_1);
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
}
else
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
return x_3;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_Elab_Command_mkCommandElabAttribute___spec__3(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_Array_empty___closed__1;
lean_inc(x_11);
x_13 = lean_apply_1(x_11, x_12);
x_14 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_15 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4(x_15, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
x_24 = lean_io_ref_get(x_3, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_io_ref_reset(x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_30 = x_23;
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_io_ref_set(x_3, x_31, x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
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
lean_dec(x_25);
lean_dec(x_23);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
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
lean_dec(x_23);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
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
lean_dec(x_11);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_Lean_Name_toString___closed__1;
x_55 = l_Lean_Name_toStringWithSep___main(x_54, x_53);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_59 = lean_string_append(x_57, x_58);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_59);
return x_4;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = lean_array_get_size(x_60);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_anyRangeMAux___main___at_Lean_Elab_Command_mkCommandElabAttribute___spec__3(x_1, x_60, x_60, x_62, x_63);
lean_dec(x_62);
lean_dec(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = l_Array_empty___closed__1;
lean_inc(x_65);
x_67 = lean_apply_1(x_65, x_66);
x_68 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_69 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
x_70 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4(x_69, x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 4);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_65);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set(x_77, 5, x_76);
x_78 = lean_io_ref_get(x_3, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_io_ref_reset(x_3, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_77);
x_84 = x_77;
x_85 = lean_array_push(x_79, x_84);
x_86 = lean_io_ref_set(x_3, x_85, x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
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
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_79);
lean_dec(x_77);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_96 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_77);
x_98 = lean_ctor_get(x_78, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_100 = x_78;
} else {
 lean_dec_ref(x_78);
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
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_65);
lean_dec(x_1);
x_102 = lean_ctor_get(x_70, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_70, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_104 = x_70;
} else {
 lean_dec_ref(x_70);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_Lean_Name_toString___closed__1;
x_108 = l_Lean_Name_toStringWithSep___main(x_107, x_106);
x_109 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_110 = lean_string_append(x_109, x_108);
lean_dec(x_108);
x_111 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_112 = lean_string_append(x_110, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_61);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_4);
if (x_114 == 0)
{
return x_4;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Command_mkCommandElabAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_3);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_6);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__2(x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_2);
x_14 = lean_string_append(x_2, x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Lean_AttributeImpl_inhabited___closed__1;
x_18 = l_Lean_AttributeImpl_inhabited___closed__4;
x_19 = l_Lean_AttributeImpl_inhabited___closed__5;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_18);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*8, x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_2);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_2);
x_26 = lean_string_append(x_2, x_25);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_27, 0, x_1);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_28, 0, x_1);
x_29 = l_Lean_AttributeImpl_inhabited___closed__1;
x_30 = l_Lean_AttributeImpl_inhabited___closed__4;
x_31 = l_Lean_AttributeImpl_inhabited___closed__5;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set(x_33, 4, x_28);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set(x_33, 6, x_31);
lean_ctor_set(x_33, 7, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandTerm");
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
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttribute___closed__2;
x_3 = l_Lean_Parser_mkCommandParserAttribute___closed__4;
x_4 = l_Lean_Elab_Command_builtinCommandElabTable;
x_5 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Command_mkCommandElabAttribute___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Command_mkCommandElabAttribute___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Command_mkCommandElabAttribute___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Command_commandElabAttribute___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
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
lean_object* _init_l_Lean_Elab_Command_commandElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__6;
x_2 = l_Lean_Elab_Command_commandElabAttribute___closed__2;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_elabCommand___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
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
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_box(0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_FileMap_toPosition(x_7, x_8);
lean_dec(x_8);
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
lean_dec(x_8);
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
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Command_elabCommand___spec__3(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4(x_1, x_2, x_9, x_4, x_8);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__7(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
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
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__7(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
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
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__8(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__7(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__10(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__9(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__9(x_8, x_2);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_Elab_Command_commandElabAttribute;
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = l_Lean_PersistentEnvExtension_getState___rarg(x_6, x_7);
lean_dec(x_7);
x_9 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_8, x_4);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_4);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Command_elabCommand___closed__6;
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Term_elabTerm___closed__6;
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_17, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_apply_3(x_19, x_1, x_2, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Command_elabCommand___closed__3;
x_22 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_21, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Command_elabCommand___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Command_elabCommand___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Command_elabCommand___spec__7(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Command_elabCommand___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_Scope_inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_3);
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
lean_object* l___private_Init_Lean_Elab_Command_1__mkTermContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 5);
lean_inc(x_8);
lean_dec(x_4);
x_9 = 1;
x_10 = 0;
x_11 = 1;
x_12 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 1, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 2, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 3, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 6, x_11);
x_13 = l_Lean_LocalContext_Inhabited___closed__2;
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_box(0);
x_20 = l_Lean_Unhygienic_run___rarg___closed__1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_6);
lean_ctor_set(x_21, 5, x_8);
lean_ctor_set(x_21, 6, x_7);
lean_ctor_set(x_21, 7, x_19);
lean_ctor_set(x_21, 8, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*9, x_9);
return x_21;
}
}
lean_object* l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_1__mkTermContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_1__mkTermContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_2__mkTermState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_MetavarContext_Inhabited___closed__1;
x_5 = l_Lean_Meta_MetaHasEval___rarg___closed__4;
x_6 = l_Lean_NameGenerator_Inhabited___closed__3;
x_7 = l_Lean_TraceState_Inhabited___closed__1;
x_8 = l_PersistentArray_empty___closed__3;
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_11);
lean_ctor_set(x_12, 5, x_11);
return x_12;
}
}
lean_object* l___private_Init_Lean_Elab_Command_2__mkTermState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Command_2__mkTermState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_3__getVarDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(x_2);
x_4 = lean_ctor_get(x_3, 6);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Command_3__getVarDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Command_3__getVarDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg___closed__1() {
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
lean_object* l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_2, 1, x_14);
return x_2;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_20 = x_1;
} else {
 lean_dec_ref(x_1);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 4, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_25, 2);
lean_inc(x_30);
lean_dec(x_25);
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_1, 0);
lean_dec(x_33);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_29);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_28);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_2, 1, x_36);
lean_ctor_set(x_2, 0, x_28);
return x_2;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_44 = x_1;
} else {
 lean_dec_ref(x_1);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 4, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg___closed__1;
x_48 = l_unreachable_x21___rarg(x_47);
return x_48;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_4__toCommandResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg), 2, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_4__toCommandResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Command_4__toCommandResult(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_28; lean_object* x_29; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = l___private_Init_Lean_Elab_Command_3__getVarDecls(x_3);
x_6 = l___private_Init_Lean_Elab_Command_1__mkTermContext(x_2, x_3);
x_7 = l___private_Init_Lean_Elab_Command_2__mkTermState(x_3);
x_8 = l_Lean_Elab_Term_getTraceState___rarg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_45 = l_Lean_TraceState_Inhabited___closed__1;
x_46 = l_Lean_Elab_Term_setTraceState(x_45, x_6, x_10);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Term_getLCtx(x_6, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Term_getLocalInsts(x_6, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_52);
x_56 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_5, x_54, x_55, x_49, x_52, x_6, x_53);
lean_dec(x_5);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_array_get_size(x_52);
lean_dec(x_52);
x_63 = lean_array_get_size(x_61);
x_64 = lean_nat_dec_lt(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_6, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_6, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_6, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_6, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_6, 8);
lean_inc(x_69);
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_65, 2);
lean_dec(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_dec(x_72);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 1, x_60);
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_box(0);
x_76 = 1;
lean_inc(x_74);
lean_inc(x_73);
x_77 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_4);
lean_ctor_set(x_77, 4, x_66);
lean_ctor_set(x_77, 5, x_67);
lean_ctor_set(x_77, 6, x_68);
lean_ctor_set(x_77, 7, x_75);
lean_ctor_set(x_77, 8, x_69);
lean_ctor_set_uint8(x_77, sizeof(void*)*9, x_76);
x_78 = lean_apply_2(x_1, x_77, x_59);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_28 = x_79;
x_29 = x_80;
goto block_44;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_11 = x_81;
x_12 = x_82;
goto block_27;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_65, 0);
lean_inc(x_83);
lean_dec(x_65);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_60);
lean_ctor_set(x_84, 2, x_61);
x_85 = lean_ctor_get(x_2, 0);
x_86 = lean_ctor_get(x_2, 1);
x_87 = lean_box(0);
x_88 = 1;
lean_inc(x_86);
lean_inc(x_85);
x_89 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_4);
lean_ctor_set(x_89, 4, x_66);
lean_ctor_set(x_89, 5, x_67);
lean_ctor_set(x_89, 6, x_68);
lean_ctor_set(x_89, 7, x_87);
lean_ctor_set(x_89, 8, x_69);
lean_ctor_set_uint8(x_89, sizeof(void*)*9, x_88);
x_90 = lean_apply_2(x_1, x_89, x_59);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_28 = x_91;
x_29 = x_92;
goto block_44;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_11 = x_93;
x_12 = x_94;
goto block_27;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_95 = lean_ctor_get(x_59, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 2);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_96, 2);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_59);
x_99 = lean_ctor_get(x_6, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_6, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_6, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_6, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_6, 8);
lean_inc(x_104);
x_105 = !lean_is_exclusive(x_99);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_99, 2);
lean_dec(x_106);
x_107 = lean_ctor_get(x_99, 1);
lean_dec(x_107);
lean_ctor_set(x_99, 2, x_61);
lean_ctor_set(x_99, 1, x_60);
x_108 = lean_ctor_get(x_2, 0);
x_109 = lean_ctor_get(x_2, 1);
x_110 = lean_box(0);
x_111 = 1;
lean_inc(x_109);
lean_inc(x_108);
x_112 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_4);
lean_ctor_set(x_112, 4, x_101);
lean_ctor_set(x_112, 5, x_102);
lean_ctor_set(x_112, 6, x_103);
lean_ctor_set(x_112, 7, x_110);
lean_ctor_set(x_112, 8, x_104);
lean_ctor_set_uint8(x_112, sizeof(void*)*9, x_111);
x_113 = lean_apply_2(x_1, x_112, x_100);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
lean_dec(x_113);
x_118 = !lean_is_exclusive(x_114);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_114, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_115);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_115, 2);
lean_dec(x_121);
x_122 = !lean_is_exclusive(x_116);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_116, 2);
lean_dec(x_123);
lean_ctor_set(x_116, 2, x_97);
x_28 = x_117;
x_29 = x_114;
goto block_44;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_116, 0);
x_125 = lean_ctor_get(x_116, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_116);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_97);
lean_ctor_set(x_115, 2, x_126);
x_28 = x_117;
x_29 = x_114;
goto block_44;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_127 = lean_ctor_get(x_115, 0);
x_128 = lean_ctor_get(x_115, 1);
x_129 = lean_ctor_get(x_115, 3);
x_130 = lean_ctor_get(x_115, 4);
x_131 = lean_ctor_get(x_115, 5);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_115);
x_132 = lean_ctor_get(x_116, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_116, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 x_134 = x_116;
} else {
 lean_dec_ref(x_116);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 3, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_97);
x_136 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_136, 3, x_129);
lean_ctor_set(x_136, 4, x_130);
lean_ctor_set(x_136, 5, x_131);
lean_ctor_set(x_114, 0, x_136);
x_28 = x_117;
x_29 = x_114;
goto block_44;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_137 = lean_ctor_get(x_114, 1);
x_138 = lean_ctor_get(x_114, 2);
x_139 = lean_ctor_get(x_114, 3);
x_140 = lean_ctor_get(x_114, 4);
x_141 = lean_ctor_get(x_114, 5);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_114);
x_142 = lean_ctor_get(x_115, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_115, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_115, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_115, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_115, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 x_147 = x_115;
} else {
 lean_dec_ref(x_115);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_116, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_116, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 x_150 = x_116;
} else {
 lean_dec_ref(x_116);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 3, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
lean_ctor_set(x_151, 2, x_97);
if (lean_is_scalar(x_147)) {
 x_152 = lean_alloc_ctor(0, 6, 0);
} else {
 x_152 = x_147;
}
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_143);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_144);
lean_ctor_set(x_152, 4, x_145);
lean_ctor_set(x_152, 5, x_146);
x_153 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_137);
lean_ctor_set(x_153, 2, x_138);
lean_ctor_set(x_153, 3, x_139);
lean_ctor_set(x_153, 4, x_140);
lean_ctor_set(x_153, 5, x_141);
x_28 = x_117;
x_29 = x_153;
goto block_44;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_154 = lean_ctor_get(x_113, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_113, 0);
lean_inc(x_157);
lean_dec(x_113);
x_158 = !lean_is_exclusive(x_154);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_154, 0);
lean_dec(x_159);
x_160 = !lean_is_exclusive(x_155);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_155, 2);
lean_dec(x_161);
x_162 = !lean_is_exclusive(x_156);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_156, 2);
lean_dec(x_163);
lean_ctor_set(x_156, 2, x_97);
x_11 = x_157;
x_12 = x_154;
goto block_27;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_156, 0);
x_165 = lean_ctor_get(x_156, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_156);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_97);
lean_ctor_set(x_155, 2, x_166);
x_11 = x_157;
x_12 = x_154;
goto block_27;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_167 = lean_ctor_get(x_155, 0);
x_168 = lean_ctor_get(x_155, 1);
x_169 = lean_ctor_get(x_155, 3);
x_170 = lean_ctor_get(x_155, 4);
x_171 = lean_ctor_get(x_155, 5);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_155);
x_172 = lean_ctor_get(x_156, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_156, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 x_174 = x_156;
} else {
 lean_dec_ref(x_156);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(0, 3, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_97);
x_176 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_176, 0, x_167);
lean_ctor_set(x_176, 1, x_168);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_169);
lean_ctor_set(x_176, 4, x_170);
lean_ctor_set(x_176, 5, x_171);
lean_ctor_set(x_154, 0, x_176);
x_11 = x_157;
x_12 = x_154;
goto block_27;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_177 = lean_ctor_get(x_154, 1);
x_178 = lean_ctor_get(x_154, 2);
x_179 = lean_ctor_get(x_154, 3);
x_180 = lean_ctor_get(x_154, 4);
x_181 = lean_ctor_get(x_154, 5);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_154);
x_182 = lean_ctor_get(x_155, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_155, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_155, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_155, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_155, 5);
lean_inc(x_186);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 lean_ctor_release(x_155, 5);
 x_187 = x_155;
} else {
 lean_dec_ref(x_155);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_156, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_156, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 x_190 = x_156;
} else {
 lean_dec_ref(x_156);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 3, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
lean_ctor_set(x_191, 2, x_97);
if (lean_is_scalar(x_187)) {
 x_192 = lean_alloc_ctor(0, 6, 0);
} else {
 x_192 = x_187;
}
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_183);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_192, 3, x_184);
lean_ctor_set(x_192, 4, x_185);
lean_ctor_set(x_192, 5, x_186);
x_193 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_177);
lean_ctor_set(x_193, 2, x_178);
lean_ctor_set(x_193, 3, x_179);
lean_ctor_set(x_193, 4, x_180);
lean_ctor_set(x_193, 5, x_181);
x_11 = x_157;
x_12 = x_193;
goto block_27;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
x_194 = lean_ctor_get(x_99, 0);
lean_inc(x_194);
lean_dec(x_99);
x_195 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_60);
lean_ctor_set(x_195, 2, x_61);
x_196 = lean_ctor_get(x_2, 0);
x_197 = lean_ctor_get(x_2, 1);
x_198 = lean_box(0);
x_199 = 1;
lean_inc(x_197);
lean_inc(x_196);
x_200 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_196);
lean_ctor_set(x_200, 2, x_197);
lean_ctor_set(x_200, 3, x_4);
lean_ctor_set(x_200, 4, x_101);
lean_ctor_set(x_200, 5, x_102);
lean_ctor_set(x_200, 6, x_103);
lean_ctor_set(x_200, 7, x_198);
lean_ctor_set(x_200, 8, x_104);
lean_ctor_set_uint8(x_200, sizeof(void*)*9, x_199);
x_201 = lean_apply_2(x_1, x_200, x_100);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_203, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
lean_dec(x_201);
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_202, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_202, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_202, 4);
lean_inc(x_209);
x_210 = lean_ctor_get(x_202, 5);
lean_inc(x_210);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 lean_ctor_release(x_202, 4);
 lean_ctor_release(x_202, 5);
 x_211 = x_202;
} else {
 lean_dec_ref(x_202);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_203, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_203, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_203, 3);
lean_inc(x_214);
x_215 = lean_ctor_get(x_203, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_203, 5);
lean_inc(x_216);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 lean_ctor_release(x_203, 3);
 lean_ctor_release(x_203, 4);
 lean_ctor_release(x_203, 5);
 x_217 = x_203;
} else {
 lean_dec_ref(x_203);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_204, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_204, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 lean_ctor_release(x_204, 2);
 x_220 = x_204;
} else {
 lean_dec_ref(x_204);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 3, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set(x_221, 2, x_97);
if (lean_is_scalar(x_217)) {
 x_222 = lean_alloc_ctor(0, 6, 0);
} else {
 x_222 = x_217;
}
lean_ctor_set(x_222, 0, x_212);
lean_ctor_set(x_222, 1, x_213);
lean_ctor_set(x_222, 2, x_221);
lean_ctor_set(x_222, 3, x_214);
lean_ctor_set(x_222, 4, x_215);
lean_ctor_set(x_222, 5, x_216);
if (lean_is_scalar(x_211)) {
 x_223 = lean_alloc_ctor(0, 6, 0);
} else {
 x_223 = x_211;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_206);
lean_ctor_set(x_223, 2, x_207);
lean_ctor_set(x_223, 3, x_208);
lean_ctor_set(x_223, 4, x_209);
lean_ctor_set(x_223, 5, x_210);
x_28 = x_205;
x_29 = x_223;
goto block_44;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_224 = lean_ctor_get(x_201, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_201, 0);
lean_inc(x_227);
lean_dec(x_201);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_224, 4);
lean_inc(x_231);
x_232 = lean_ctor_get(x_224, 5);
lean_inc(x_232);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 lean_ctor_release(x_224, 3);
 lean_ctor_release(x_224, 4);
 lean_ctor_release(x_224, 5);
 x_233 = x_224;
} else {
 lean_dec_ref(x_224);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_225, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_225, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_225, 4);
lean_inc(x_237);
x_238 = lean_ctor_get(x_225, 5);
lean_inc(x_238);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 lean_ctor_release(x_225, 4);
 lean_ctor_release(x_225, 5);
 x_239 = x_225;
} else {
 lean_dec_ref(x_225);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_226, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_226, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 x_242 = x_226;
} else {
 lean_dec_ref(x_226);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set(x_243, 2, x_97);
if (lean_is_scalar(x_239)) {
 x_244 = lean_alloc_ctor(0, 6, 0);
} else {
 x_244 = x_239;
}
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_235);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_236);
lean_ctor_set(x_244, 4, x_237);
lean_ctor_set(x_244, 5, x_238);
if (lean_is_scalar(x_233)) {
 x_245 = lean_alloc_ctor(0, 6, 0);
} else {
 x_245 = x_233;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_228);
lean_ctor_set(x_245, 2, x_229);
lean_ctor_set(x_245, 3, x_230);
lean_ctor_set(x_245, 4, x_231);
lean_ctor_set(x_245, 5, x_232);
x_11 = x_227;
x_12 = x_245;
goto block_27;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_52);
lean_dec(x_4);
lean_dec(x_1);
x_246 = lean_ctor_get(x_56, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_56, 1);
lean_inc(x_247);
lean_dec(x_56);
x_11 = x_246;
x_12 = x_247;
goto block_27;
}
block_27:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = l_Lean_Elab_Term_getTraceState___rarg(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_18 = l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__1(x_3, x_16, x_17, x_6, x_15);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Term_setTraceState(x_9, x_6, x_19);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_11);
x_23 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_25);
return x_26;
}
}
block_44:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = l_Lean_Elab_Term_getTraceState___rarg(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_35 = l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__2(x_3, x_33, x_34, x_6, x_32);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Term_setTraceState(x_9, x_6, x_36);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_28);
x_40 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_runTermElabM___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_runTermElabM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_Elab_Command_getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getEnv___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_setEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Command_setEnv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_setEnv(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(x_2);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScope___rarg), 1, 0);
return x_2;
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
lean_object* l_Lean_Elab_Command_getCurrNamespace___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Command_getScope___rarg(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_5);
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
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Command_getCurrNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getCurrNamespace___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getCurrNamespace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getCurrNamespace(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Command_5__addScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_3);
x_9 = l_Lean_Environment_registerNamespace___main(x_7, x_3);
x_10 = l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
lean_ctor_set(x_10, 3, x_3);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 0, x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_5, 3, x_15);
lean_ctor_set(x_5, 0, x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 4);
x_20 = lean_ctor_get(x_10, 5);
x_21 = lean_ctor_get(x_10, 6);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_3);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_20);
lean_ctor_set(x_22, 6, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_5, 3, x_23);
lean_ctor_set(x_5, 0, x_9);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 2);
x_29 = lean_ctor_get(x_5, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
lean_inc(x_3);
x_30 = l_Lean_Environment_registerNamespace___main(x_26, x_3);
x_31 = l_List_head_x21___at___private_Init_Lean_Elab_Command_1__mkTermContext___spec__1(x_29);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 6);
lean_inc(x_35);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 lean_ctor_release(x_31, 4);
 lean_ctor_release(x_31, 5);
 lean_ctor_release(x_31, 6);
 x_36 = x_31;
} else {
 lean_dec_ref(x_31);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 7, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_3);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set(x_37, 6, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_5__addScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Command_5__addScope(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Command_6__addScopes___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2___closed__1;
x_2 = l_PUnit_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l___private_Init_Lean_Elab_Command_6__addScopes___main(x_1, x_2, x_8, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_getCurrNamespace___rarg(x_11);
if (x_2 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Init_Lean_Elab_Command_5__addScope(x_1, x_9, x_13, x_4, x_14);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
lean_inc(x_9);
x_19 = lean_name_mk_string(x_18, x_9);
x_20 = l_Lean_Name_append___main(x_16, x_19);
lean_dec(x_16);
x_21 = l___private_Init_Lean_Elab_Command_5__addScope(x_1, x_9, x_20, x_4, x_17);
lean_dec(x_4);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
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
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_26 = l___private_Init_Lean_Elab_Command_6__addScopes___main___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_apply_2(x_27, x_4, x_5);
return x_28;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Init_Lean_Elab_Command_6__addScopes___main(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Command_6__addScopes___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Command_6__addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Init_Lean_Elab_Command_6__addScopes(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_10 = 1;
x_11 = l___private_Init_Lean_Elab_Command_6__addScopes___main(x_9, x_10, x_8, x_2, x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabNamespace(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNamespace___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabNamespace___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getOptionalIdent(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Elab_Command_getCurrNamespace___rarg(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_13 = l_String_splitAux___main___closed__1;
x_14 = l___private_Init_Lean_Elab_Command_5__addScope(x_12, x_13, x_10, x_2, x_11);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_17 = 0;
x_18 = l___private_Init_Lean_Elab_Command_6__addScopes___main(x_16, x_17, x_15, x_2, x_3);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabSection(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSection___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabSection___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getScopes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScopes___rarg), 1, 0);
return x_2;
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
uint8_t l___private_Init_Lean_Elab_Command_7__checkAnonymousScope(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_Command_7__checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Command_7__checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Elab_Command_8__checkEndHeader___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Lean_Elab_Command_8__checkEndHeader___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_Command_8__checkEndHeader___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Elab_Command_8__checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Elab_Command_8__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Command_8__checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_Command_8__checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabEnd___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
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
x_5 = l_Lean_Elab_Command_getScopes___rarg(x_3);
x_6 = l_Lean_stxInh;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_4, x_7);
x_9 = l_Lean_Syntax_getOptionalIdent(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_5, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_5, 1);
lean_inc(x_65);
lean_dec(x_5);
x_10 = x_7;
x_11 = x_64;
x_12 = x_65;
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_9, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_5, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
lean_dec(x_5);
x_69 = l_Lean_Name_getNumParts___main(x_66);
lean_dec(x_66);
x_10 = x_69;
x_11 = x_67;
x_12 = x_68;
goto block_63;
}
block_63:
{
lean_object* x_13; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_List_lengthAux___main___rarg(x_11, x_26);
x_28 = lean_nat_dec_lt(x_10, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_12, 3);
x_31 = l_List_lengthAux___main___rarg(x_30, x_26);
x_32 = lean_nat_sub(x_31, x_7);
lean_dec(x_31);
x_33 = l_List_drop___main___rarg(x_32, x_30);
lean_dec(x_30);
lean_ctor_set(x_12, 3, x_33);
x_34 = l_Lean_Elab_Command_elabEnd___closed__9;
x_35 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_1, x_34, x_2, x_12);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
x_42 = lean_ctor_get(x_12, 2);
x_43 = lean_ctor_get(x_12, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_44 = l_List_lengthAux___main___rarg(x_43, x_26);
x_45 = lean_nat_sub(x_44, x_7);
lean_dec(x_44);
x_46 = l_List_drop___main___rarg(x_45, x_43);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Lean_Elab_Command_elabEnd___closed__9;
x_49 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_1, x_48, x_2, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
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
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_12, 3);
x_56 = l_List_drop___main___rarg(x_10, x_55);
lean_dec(x_55);
lean_ctor_set(x_12, 3, x_56);
x_13 = x_12;
goto block_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
x_59 = lean_ctor_get(x_12, 2);
x_60 = lean_ctor_get(x_12, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_61 = l_List_drop___main___rarg(x_10, x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_13 = x_62;
goto block_25;
}
}
block_25:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_14; 
x_14 = l___private_Init_Lean_Elab_Command_7__checkAnonymousScope(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_Command_elabEnd___closed__3;
x_16 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_15, x_2, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
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
x_20 = l___private_Init_Lean_Elab_Command_8__checkEndHeader___main(x_19, x_11);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Command_elabEnd___closed__6;
x_22 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_21, x_2, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
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
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabEnd___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabEnd(x_1, x_2, x_3);
lean_dec(x_2);
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
x_2 = l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabEnd___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
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
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 3);
lean_dec(x_6);
x_7 = l_Lean_Elab_Command_modifyScope___closed__1;
x_8 = l_unreachable_x21___rarg(x_7);
lean_ctor_set(x_3, 3, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l_Lean_Elab_Command_modifyScope___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
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
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_3, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_apply_1(x_1, x_22);
lean_ctor_set(x_4, 0, x_23);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_apply_1(x_1, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_3, 3, x_29);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_ctor_get(x_3, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_37 = x_4;
} else {
 lean_dec_ref(x_4);
 x_37 = lean_box(0);
}
x_38 = lean_apply_1(x_1, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_34);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getUniverseNames___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Command_getScope___rarg(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 5);
lean_inc(x_5);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_5);
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
x_8 = lean_ctor_get(x_6, 5);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Command_getUniverseNames(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getUniverseNames___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getUniverseNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getUniverseNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUniverse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 3);
lean_dec(x_6);
x_7 = l_Lean_Elab_Command_modifyScope___closed__1;
x_8 = l_unreachable_x21___rarg(x_7);
lean_ctor_set(x_3, 3, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l_Lean_Elab_Command_modifyScope___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_3, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 5);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_19, 5, x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_3, 3, x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
x_32 = lean_ctor_get(x_19, 2);
x_33 = lean_ctor_get(x_19, 3);
x_34 = lean_ctor_get(x_19, 4);
x_35 = lean_ctor_get(x_19, 5);
x_36 = lean_ctor_get(x_19, 6);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
lean_ctor_set(x_4, 1, x_35);
lean_ctor_set(x_4, 0, x_1);
x_37 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_34);
lean_ctor_set(x_37, 5, x_4);
lean_ctor_set(x_37, 6, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_3, 3, x_38);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_19, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_19, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_19, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_19, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_49 = x_19;
} else {
 lean_dec_ref(x_19);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_47);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 7, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_51, 6, x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_3, 3, x_52);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_55 = lean_ctor_get(x_3, 0);
x_56 = lean_ctor_get(x_3, 1);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_3);
x_58 = lean_ctor_get(x_4, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_59 = x_4;
} else {
 lean_dec_ref(x_4);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_19, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_19, 6);
lean_inc(x_66);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_67 = x_19;
} else {
 lean_dec_ref(x_19);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_59;
}
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_65);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 7, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set(x_69, 5, x_68);
lean_ctor_set(x_69, 6, x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_58);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_56);
lean_ctor_set(x_71, 2, x_57);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_addUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a universe named '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_addUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_addUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_addUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_addUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_addUniverse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared in this Scope");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_addUniverse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_addUniverse___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_addUniverse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_addUniverse___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_addUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Syntax_getId(x_1);
x_5 = l_Lean_Elab_Command_getUniverseNames___rarg(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUniverse___spec__1(x_4, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_4);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Command_addUniverse___closed__3;
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Command_addUniverse___closed__6;
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_17, x_2, x_7);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUniverse___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_addUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_addUniverse(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
x_8 = l_Lean_Elab_Command_addUniverse(x_7, x_2, x_3);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabUniverse(x_1, x_2, x_3);
lean_dec(x_2);
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
x_2 = l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
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
x_11 = l_Lean_Elab_Command_addUniverse(x_10, x_5, x_6);
lean_dec(x_10);
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
lean_dec(x_5);
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
lean_dec(x_2);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Elab_Command_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(4);
x_8 = lean_add_decl(x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_KernelException_toMessageData(x_9);
x_11 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_10, x_2, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Elab_Command_setEnv(x_12, x_2, x_6);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabInitQuot(x_1, x_2, x_3);
lean_dec(x_2);
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
x_2 = l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabInitQuot___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getOpenDecls___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Command_getScope___rarg(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_5);
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
x_8 = lean_ctor_get(x_6, 4);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Command_getOpenDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getOpenDecls___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getOpenDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getOpenDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_logUnknownDecl___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4(x_3, x_2, x_6, x_4, x_5);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_9, 1, x_13);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_box(0);
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 x_29 = x_23;
} else {
 lean_dec_ref(x_23);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_26);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 4, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Command_elabCommand___spec__3(x_1, x_4, x_5);
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
x_11 = l_Lean_Elab_Term_mkConst___closed__4;
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
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_logUnknownDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = 2;
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Command_elabCommand___spec__4(x_1, x_6, x_5, x_2, x_3);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Elab_Command_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Command_getCurrNamespace___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getOpenDecls___rarg(x_9);
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
x_21 = l_Lean_Elab_Term_mkConst___closed__4;
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(x_22, x_2, x_13);
return x_23;
}
else
{
lean_object* x_24; 
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
x_34 = l_Lean_Elab_Term_mkConst___closed__4;
x_35 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_throwErrorUsingCmdPos___at_Lean_Elab_Command_resolveNamespace___spec__1(x_35, x_2, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
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
lean_object* l_Lean_Elab_Command_resolveNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_resolveNamespace(x_1, x_2, x_3);
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
lean_dec(x_6);
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
x_18 = l_Lean_Environment_contains(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = l_Lean_Elab_Command_logUnknownDecl(x_13, x_17, x_8, x_9);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_6 = x_15;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_22 = l_Lean_Name_append___main(x_3, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
x_6 = x_15;
x_7 = x_24;
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
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_52; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_getCurrNamespace___rarg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_52 = lean_name_eq(x_10, x_13);
if (x_52 == 0)
{
x_15 = x_14;
goto block_51;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_10);
x_53 = l_Lean_Elab_Command_elabExport___closed__3;
x_54 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_53, x_2, x_14);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
block_51:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = l_Lean_Elab_Command_getEnv___rarg(x_15);
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
x_24 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(x_4, x_10, x_13, x_17, x_22, x_23, x_19, x_2, x_18);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_29, x_28);
lean_ctor_set(x_26, 0, x_30);
x_31 = lean_box(0);
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
x_35 = lean_ctor_get(x_26, 2);
x_36 = lean_ctor_get(x_26, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_37 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_33, x_32);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
x_39 = lean_box(0);
lean_ctor_set(x_24, 1, x_38);
lean_ctor_set(x_24, 0, x_39);
return x_24;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_24, 1);
x_41 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 3);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
x_47 = l_List_foldl___main___at_Lean_Elab_Command_elabExport___spec__2(x_42, x_41);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 4, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_9);
if (x_59 == 0)
{
return x_9;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_9, 0);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_9);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_2);
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
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 3);
lean_dec(x_6);
x_7 = l_Lean_Elab_Command_modifyScope___closed__1;
x_8 = l_unreachable_x21___rarg(x_7);
lean_ctor_set(x_3, 3, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l_Lean_Elab_Command_modifyScope___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_3, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 4);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_19, 4, x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_3, 3, x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
x_32 = lean_ctor_get(x_19, 2);
x_33 = lean_ctor_get(x_19, 3);
x_34 = lean_ctor_get(x_19, 4);
x_35 = lean_ctor_get(x_19, 5);
x_36 = lean_ctor_get(x_19, 6);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
lean_ctor_set(x_4, 1, x_34);
lean_ctor_set(x_4, 0, x_1);
x_37 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_4);
lean_ctor_set(x_37, 5, x_35);
lean_ctor_set(x_37, 6, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_3, 3, x_38);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_19, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_19, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_19, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_19, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_49 = x_19;
} else {
 lean_dec_ref(x_19);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_46);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 7, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_47);
lean_ctor_set(x_51, 6, x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_3, 3, x_52);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_55 = lean_ctor_get(x_3, 0);
x_56 = lean_ctor_get(x_3, 1);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_3);
x_58 = lean_ctor_get(x_4, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_59 = x_4;
} else {
 lean_dec_ref(x_4);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_19, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_19, 6);
lean_inc(x_66);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_67 = x_19;
} else {
 lean_dec_ref(x_19);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_59;
}
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_64);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 7, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set(x_69, 5, x_65);
lean_ctor_set(x_69, 6, x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_58);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_56);
lean_ctor_set(x_71, 2, x_57);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
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
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_addOpenDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_addOpenDecl(x_1, x_2, x_3);
lean_dec(x_2);
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
x_12 = l_Lean_Elab_Command_resolveNamespace(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_16, x_5, x_14);
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
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_dec(x_5);
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
lean_dec(x_2);
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
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = l_Lean_Syntax_getId(x_11);
lean_inc(x_12);
x_13 = l_Lean_Name_append___main(x_1, x_12);
x_14 = l_Lean_Elab_Command_getEnv___rarg(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Environment_contains(x_15, x_13);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_18 = l_Lean_Elab_Command_logUnknownDecl(x_11, x_13, x_6, x_16);
lean_dec(x_11);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
x_24 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_23, x_6, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_27;
x_5 = x_25;
x_7 = x_26;
goto _start;
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
lean_dec(x_6);
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
lean_dec(x_2);
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
lean_dec(x_5);
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
x_15 = l_Lean_Environment_contains(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_logUnknownDecl(x_12, x_14, x_7, x_8);
lean_dec(x_12);
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
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_21;
x_6 = x_20;
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
x_9 = l_Lean_Elab_Command_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_getEnv___rarg(x_11);
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
x_20 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_10, x_13, x_19, x_18, x_6, x_17, x_2, x_14);
lean_dec(x_18);
lean_dec(x_13);
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
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_2);
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
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getIdAt(x_11, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getIdAt(x_11, x_14);
x_16 = l_Lean_Name_append___main(x_1, x_13);
x_17 = l_Lean_Elab_Command_getEnv___rarg(x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Environment_contains(x_18, x_16);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_21 = l_Lean_Elab_Command_logUnknownDecl(x_11, x_16, x_6, x_19);
lean_dec(x_11);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_16);
x_27 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_26, x_6, x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_30;
x_5 = x_28;
x_7 = x_29;
goto _start;
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
lean_dec(x_6);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 3);
lean_dec(x_6);
x_7 = l_Lean_Elab_Command_modifyScope___closed__1;
x_8 = l_unreachable_x21___rarg(x_7);
lean_ctor_set(x_3, 3, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l_Lean_Elab_Command_modifyScope___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_3, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 6);
x_26 = lean_array_push(x_25, x_1);
lean_ctor_set(x_19, 6, x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
x_31 = lean_ctor_get(x_19, 2);
x_32 = lean_ctor_get(x_19, 3);
x_33 = lean_ctor_get(x_19, 4);
x_34 = lean_ctor_get(x_19, 5);
x_35 = lean_ctor_get(x_19, 6);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_36 = lean_array_push(x_35, x_1);
x_37 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set(x_37, 6, x_36);
lean_ctor_set(x_4, 0, x_37);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_ctor_get(x_19, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_19, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_19, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_19, 6);
lean_inc(x_47);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_48 = x_19;
} else {
 lean_dec_ref(x_19);
 x_48 = lean_box(0);
}
x_49 = lean_array_push(x_47, x_1);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 7, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_3, 3, x_51);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_54 = lean_ctor_get(x_3, 0);
x_55 = lean_ctor_get(x_3, 1);
x_56 = lean_ctor_get(x_3, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_3);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_58 = x_4;
} else {
 lean_dec_ref(x_4);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_19, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_19, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_19, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_19, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 6);
lean_inc(x_65);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_66 = x_19;
} else {
 lean_dec_ref(x_19);
 x_66 = lean_box(0);
}
x_67 = lean_array_push(x_65, x_1);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 7, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_62);
lean_ctor_set(x_68, 4, x_63);
lean_ctor_set(x_68, 5, x_64);
lean_ctor_set(x_68, 6, x_67);
if (lean_is_scalar(x_58)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_58;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_57);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_56);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_40; lean_object* x_41; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = l___private_Init_Lean_Elab_Command_3__getVarDecls(x_3);
x_7 = l___private_Init_Lean_Elab_Command_1__mkTermContext(x_2, x_3);
x_8 = l___private_Init_Lean_Elab_Command_2__mkTermState(x_3);
x_9 = l_Lean_Elab_Term_getTraceState___rarg(x_8);
x_10 = l_Lean_stxInh;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_array_get(x_10, x_4, x_11);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_57 = l_Lean_TraceState_Inhabited___closed__1;
x_58 = l_Lean_Elab_Term_setTraceState(x_57, x_7, x_22);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Elab_Term_getLCtx(x_7, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Elab_Term_getLocalInsts(x_7, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_empty___closed__1;
lean_inc(x_7);
lean_inc(x_64);
x_68 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_6, x_66, x_67, x_61, x_64, x_7, x_65);
lean_dec(x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_array_get_size(x_64);
lean_dec(x_64);
x_75 = lean_array_get_size(x_73);
x_76 = lean_nat_dec_lt(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_7, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_7, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_7, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_7, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_7, 8);
lean_inc(x_81);
x_82 = !lean_is_exclusive(x_77);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_83 = lean_ctor_get(x_77, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_dec(x_84);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 1, x_72);
x_85 = lean_ctor_get(x_2, 0);
x_86 = lean_ctor_get(x_2, 1);
x_87 = lean_box(0);
x_88 = 1;
lean_inc(x_86);
lean_inc(x_85);
x_89 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_5);
lean_ctor_set(x_89, 4, x_78);
lean_ctor_set(x_89, 5, x_79);
lean_ctor_set(x_89, 6, x_80);
lean_ctor_set(x_89, 7, x_87);
lean_ctor_set(x_89, 8, x_81);
lean_ctor_set_uint8(x_89, sizeof(void*)*9, x_88);
x_90 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_12);
x_91 = lean_array_push(x_90, x_12);
x_92 = l_Lean_Elab_Term_getLCtx(x_89, x_71);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Elab_Term_getLocalInsts(x_89, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_96);
x_98 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_91, x_66, x_67, x_93, x_96, x_89, x_97);
lean_dec(x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_array_get_size(x_96);
lean_dec(x_96);
x_104 = lean_array_get_size(x_102);
lean_dec(x_102);
x_105 = lean_nat_dec_lt(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_box(0);
x_40 = x_106;
x_41 = x_101;
goto block_56;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get(x_108, 2);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_101);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 2);
lean_inc(x_113);
x_114 = !lean_is_exclusive(x_111);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_111, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_112);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_112, 2);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_113);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_113, 2);
lean_dec(x_119);
lean_ctor_set(x_113, 2, x_109);
x_120 = lean_box(0);
x_40 = x_120;
x_41 = x_111;
goto block_56;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_113, 0);
x_122 = lean_ctor_get(x_113, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_113);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_109);
lean_ctor_set(x_112, 2, x_123);
x_124 = lean_box(0);
x_40 = x_124;
x_41 = x_111;
goto block_56;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_125 = lean_ctor_get(x_112, 0);
x_126 = lean_ctor_get(x_112, 1);
x_127 = lean_ctor_get(x_112, 3);
x_128 = lean_ctor_get(x_112, 4);
x_129 = lean_ctor_get(x_112, 5);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_112);
x_130 = lean_ctor_get(x_113, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_113, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 x_132 = x_113;
} else {
 lean_dec_ref(x_113);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
lean_ctor_set(x_133, 2, x_109);
x_134 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_127);
lean_ctor_set(x_134, 4, x_128);
lean_ctor_set(x_134, 5, x_129);
lean_ctor_set(x_111, 0, x_134);
x_135 = lean_box(0);
x_40 = x_135;
x_41 = x_111;
goto block_56;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_136 = lean_ctor_get(x_111, 1);
x_137 = lean_ctor_get(x_111, 2);
x_138 = lean_ctor_get(x_111, 3);
x_139 = lean_ctor_get(x_111, 4);
x_140 = lean_ctor_get(x_111, 5);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_111);
x_141 = lean_ctor_get(x_112, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_112, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_112, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_112, 4);
lean_inc(x_144);
x_145 = lean_ctor_get(x_112, 5);
lean_inc(x_145);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 x_146 = x_112;
} else {
 lean_dec_ref(x_112);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_113, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_113, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 x_149 = x_113;
} else {
 lean_dec_ref(x_113);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 3, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
lean_ctor_set(x_150, 2, x_109);
if (lean_is_scalar(x_146)) {
 x_151 = lean_alloc_ctor(0, 6, 0);
} else {
 x_151 = x_146;
}
lean_ctor_set(x_151, 0, x_141);
lean_ctor_set(x_151, 1, x_142);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_151, 3, x_143);
lean_ctor_set(x_151, 4, x_144);
lean_ctor_set(x_151, 5, x_145);
x_152 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_136);
lean_ctor_set(x_152, 2, x_137);
lean_ctor_set(x_152, 3, x_138);
lean_ctor_set(x_152, 4, x_139);
lean_ctor_set(x_152, 5, x_140);
x_153 = lean_box(0);
x_40 = x_153;
x_41 = x_152;
goto block_56;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_96);
x_154 = lean_ctor_get(x_98, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_98, 1);
lean_inc(x_155);
lean_dec(x_98);
x_23 = x_154;
x_24 = x_155;
goto block_39;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_156 = lean_ctor_get(x_77, 0);
lean_inc(x_156);
lean_dec(x_77);
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_72);
lean_ctor_set(x_157, 2, x_73);
x_158 = lean_ctor_get(x_2, 0);
x_159 = lean_ctor_get(x_2, 1);
x_160 = lean_box(0);
x_161 = 1;
lean_inc(x_159);
lean_inc(x_158);
x_162 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_158);
lean_ctor_set(x_162, 2, x_159);
lean_ctor_set(x_162, 3, x_5);
lean_ctor_set(x_162, 4, x_78);
lean_ctor_set(x_162, 5, x_79);
lean_ctor_set(x_162, 6, x_80);
lean_ctor_set(x_162, 7, x_160);
lean_ctor_set(x_162, 8, x_81);
lean_ctor_set_uint8(x_162, sizeof(void*)*9, x_161);
x_163 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_12);
x_164 = lean_array_push(x_163, x_12);
x_165 = l_Lean_Elab_Term_getLCtx(x_162, x_71);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_Elab_Term_getLocalInsts(x_162, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_169);
x_171 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_164, x_66, x_67, x_166, x_169, x_162, x_170);
lean_dec(x_164);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_array_get_size(x_169);
lean_dec(x_169);
x_177 = lean_array_get_size(x_175);
lean_dec(x_175);
x_178 = lean_nat_dec_lt(x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_box(0);
x_40 = x_179;
x_41 = x_174;
goto block_56;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 2);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_ctor_get(x_181, 2);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_174);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 5);
lean_inc(x_191);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_192 = x_184;
} else {
 lean_dec_ref(x_184);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_185, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_185, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_185, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 lean_ctor_release(x_185, 5);
 x_198 = x_185;
} else {
 lean_dec_ref(x_185);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_186, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_186, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 x_201 = x_186;
} else {
 lean_dec_ref(x_186);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 3, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_182);
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_198;
}
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_194);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_195);
lean_ctor_set(x_203, 4, x_196);
lean_ctor_set(x_203, 5, x_197);
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(0, 6, 0);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_187);
lean_ctor_set(x_204, 2, x_188);
lean_ctor_set(x_204, 3, x_189);
lean_ctor_set(x_204, 4, x_190);
lean_ctor_set(x_204, 5, x_191);
x_205 = lean_box(0);
x_40 = x_205;
x_41 = x_204;
goto block_56;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_169);
x_206 = lean_ctor_get(x_171, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_171, 1);
lean_inc(x_207);
lean_dec(x_171);
x_23 = x_206;
x_24 = x_207;
goto block_39;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_252; lean_object* x_253; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_208 = lean_ctor_get(x_71, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_208, 2);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_ctor_get(x_209, 2);
lean_inc(x_210);
lean_dec(x_209);
x_293 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_71);
x_294 = lean_ctor_get(x_7, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_ctor_get(x_7, 4);
lean_inc(x_296);
x_297 = lean_ctor_get(x_7, 5);
lean_inc(x_297);
x_298 = lean_ctor_get(x_7, 6);
lean_inc(x_298);
x_299 = lean_ctor_get(x_7, 8);
lean_inc(x_299);
x_300 = !lean_is_exclusive(x_294);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_301 = lean_ctor_get(x_294, 2);
lean_dec(x_301);
x_302 = lean_ctor_get(x_294, 1);
lean_dec(x_302);
lean_ctor_set(x_294, 2, x_73);
lean_ctor_set(x_294, 1, x_72);
x_303 = lean_ctor_get(x_2, 0);
x_304 = lean_ctor_get(x_2, 1);
x_305 = lean_box(0);
x_306 = 1;
lean_inc(x_304);
lean_inc(x_303);
x_307 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_307, 0, x_294);
lean_ctor_set(x_307, 1, x_303);
lean_ctor_set(x_307, 2, x_304);
lean_ctor_set(x_307, 3, x_5);
lean_ctor_set(x_307, 4, x_296);
lean_ctor_set(x_307, 5, x_297);
lean_ctor_set(x_307, 6, x_298);
lean_ctor_set(x_307, 7, x_305);
lean_ctor_set(x_307, 8, x_299);
lean_ctor_set_uint8(x_307, sizeof(void*)*9, x_306);
x_308 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_12);
x_309 = lean_array_push(x_308, x_12);
x_310 = l_Lean_Elab_Term_getLCtx(x_307, x_295);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l_Lean_Elab_Term_getLocalInsts(x_307, x_312);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
lean_inc(x_314);
x_316 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_309, x_66, x_67, x_311, x_314, x_307, x_315);
lean_dec(x_309);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_dec(x_316);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_array_get_size(x_314);
lean_dec(x_314);
x_322 = lean_array_get_size(x_320);
lean_dec(x_320);
x_323 = lean_nat_dec_lt(x_321, x_322);
lean_dec(x_322);
lean_dec(x_321);
if (x_323 == 0)
{
lean_object* x_324; 
x_324 = lean_box(0);
x_211 = x_324;
x_212 = x_319;
goto block_251;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_325 = lean_ctor_get(x_319, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 2);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_ctor_get(x_326, 2);
lean_inc(x_327);
lean_dec(x_326);
x_328 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_319);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_330, 2);
lean_inc(x_331);
x_332 = !lean_is_exclusive(x_329);
if (x_332 == 0)
{
lean_object* x_333; uint8_t x_334; 
x_333 = lean_ctor_get(x_329, 0);
lean_dec(x_333);
x_334 = !lean_is_exclusive(x_330);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_ctor_get(x_330, 2);
lean_dec(x_335);
x_336 = !lean_is_exclusive(x_331);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_331, 2);
lean_dec(x_337);
lean_ctor_set(x_331, 2, x_327);
x_338 = lean_box(0);
x_211 = x_338;
x_212 = x_329;
goto block_251;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_331, 0);
x_340 = lean_ctor_get(x_331, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_331);
x_341 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
lean_ctor_set(x_341, 2, x_327);
lean_ctor_set(x_330, 2, x_341);
x_342 = lean_box(0);
x_211 = x_342;
x_212 = x_329;
goto block_251;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_343 = lean_ctor_get(x_330, 0);
x_344 = lean_ctor_get(x_330, 1);
x_345 = lean_ctor_get(x_330, 3);
x_346 = lean_ctor_get(x_330, 4);
x_347 = lean_ctor_get(x_330, 5);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_330);
x_348 = lean_ctor_get(x_331, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_331, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 lean_ctor_release(x_331, 2);
 x_350 = x_331;
} else {
 lean_dec_ref(x_331);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(0, 3, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
lean_ctor_set(x_351, 2, x_327);
x_352 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_352, 0, x_343);
lean_ctor_set(x_352, 1, x_344);
lean_ctor_set(x_352, 2, x_351);
lean_ctor_set(x_352, 3, x_345);
lean_ctor_set(x_352, 4, x_346);
lean_ctor_set(x_352, 5, x_347);
lean_ctor_set(x_329, 0, x_352);
x_353 = lean_box(0);
x_211 = x_353;
x_212 = x_329;
goto block_251;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_354 = lean_ctor_get(x_329, 1);
x_355 = lean_ctor_get(x_329, 2);
x_356 = lean_ctor_get(x_329, 3);
x_357 = lean_ctor_get(x_329, 4);
x_358 = lean_ctor_get(x_329, 5);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_329);
x_359 = lean_ctor_get(x_330, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_330, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_330, 3);
lean_inc(x_361);
x_362 = lean_ctor_get(x_330, 4);
lean_inc(x_362);
x_363 = lean_ctor_get(x_330, 5);
lean_inc(x_363);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 lean_ctor_release(x_330, 5);
 x_364 = x_330;
} else {
 lean_dec_ref(x_330);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_331, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_331, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 lean_ctor_release(x_331, 2);
 x_367 = x_331;
} else {
 lean_dec_ref(x_331);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 3, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
lean_ctor_set(x_368, 2, x_327);
if (lean_is_scalar(x_364)) {
 x_369 = lean_alloc_ctor(0, 6, 0);
} else {
 x_369 = x_364;
}
lean_ctor_set(x_369, 0, x_359);
lean_ctor_set(x_369, 1, x_360);
lean_ctor_set(x_369, 2, x_368);
lean_ctor_set(x_369, 3, x_361);
lean_ctor_set(x_369, 4, x_362);
lean_ctor_set(x_369, 5, x_363);
x_370 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_354);
lean_ctor_set(x_370, 2, x_355);
lean_ctor_set(x_370, 3, x_356);
lean_ctor_set(x_370, 4, x_357);
lean_ctor_set(x_370, 5, x_358);
x_371 = lean_box(0);
x_211 = x_371;
x_212 = x_370;
goto block_251;
}
}
}
else
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_314);
x_372 = lean_ctor_get(x_316, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_316, 1);
lean_inc(x_373);
lean_dec(x_316);
x_252 = x_372;
x_253 = x_373;
goto block_292;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_374 = lean_ctor_get(x_294, 0);
lean_inc(x_374);
lean_dec(x_294);
x_375 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_72);
lean_ctor_set(x_375, 2, x_73);
x_376 = lean_ctor_get(x_2, 0);
x_377 = lean_ctor_get(x_2, 1);
x_378 = lean_box(0);
x_379 = 1;
lean_inc(x_377);
lean_inc(x_376);
x_380 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_380, 0, x_375);
lean_ctor_set(x_380, 1, x_376);
lean_ctor_set(x_380, 2, x_377);
lean_ctor_set(x_380, 3, x_5);
lean_ctor_set(x_380, 4, x_296);
lean_ctor_set(x_380, 5, x_297);
lean_ctor_set(x_380, 6, x_298);
lean_ctor_set(x_380, 7, x_378);
lean_ctor_set(x_380, 8, x_299);
lean_ctor_set_uint8(x_380, sizeof(void*)*9, x_379);
x_381 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_12);
x_382 = lean_array_push(x_381, x_12);
x_383 = l_Lean_Elab_Term_getLCtx(x_380, x_295);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l_Lean_Elab_Term_getLocalInsts(x_380, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
lean_inc(x_387);
x_389 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_382, x_66, x_67, x_384, x_387, x_380, x_388);
lean_dec(x_382);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_array_get_size(x_387);
lean_dec(x_387);
x_395 = lean_array_get_size(x_393);
lean_dec(x_393);
x_396 = lean_nat_dec_lt(x_394, x_395);
lean_dec(x_395);
lean_dec(x_394);
if (x_396 == 0)
{
lean_object* x_397; 
x_397 = lean_box(0);
x_211 = x_397;
x_212 = x_392;
goto block_251;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_398 = lean_ctor_get(x_392, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_398, 2);
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_ctor_get(x_399, 2);
lean_inc(x_400);
lean_dec(x_399);
x_401 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_392);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_403, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_402, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_402, 3);
lean_inc(x_407);
x_408 = lean_ctor_get(x_402, 4);
lean_inc(x_408);
x_409 = lean_ctor_get(x_402, 5);
lean_inc(x_409);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 lean_ctor_release(x_402, 2);
 lean_ctor_release(x_402, 3);
 lean_ctor_release(x_402, 4);
 lean_ctor_release(x_402, 5);
 x_410 = x_402;
} else {
 lean_dec_ref(x_402);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_403, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_403, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_403, 3);
lean_inc(x_413);
x_414 = lean_ctor_get(x_403, 4);
lean_inc(x_414);
x_415 = lean_ctor_get(x_403, 5);
lean_inc(x_415);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 lean_ctor_release(x_403, 3);
 lean_ctor_release(x_403, 4);
 lean_ctor_release(x_403, 5);
 x_416 = x_403;
} else {
 lean_dec_ref(x_403);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_404, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_404, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 lean_ctor_release(x_404, 2);
 x_419 = x_404;
} else {
 lean_dec_ref(x_404);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(0, 3, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
lean_ctor_set(x_420, 2, x_400);
if (lean_is_scalar(x_416)) {
 x_421 = lean_alloc_ctor(0, 6, 0);
} else {
 x_421 = x_416;
}
lean_ctor_set(x_421, 0, x_411);
lean_ctor_set(x_421, 1, x_412);
lean_ctor_set(x_421, 2, x_420);
lean_ctor_set(x_421, 3, x_413);
lean_ctor_set(x_421, 4, x_414);
lean_ctor_set(x_421, 5, x_415);
if (lean_is_scalar(x_410)) {
 x_422 = lean_alloc_ctor(0, 6, 0);
} else {
 x_422 = x_410;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_405);
lean_ctor_set(x_422, 2, x_406);
lean_ctor_set(x_422, 3, x_407);
lean_ctor_set(x_422, 4, x_408);
lean_ctor_set(x_422, 5, x_409);
x_423 = lean_box(0);
x_211 = x_423;
x_212 = x_422;
goto block_251;
}
}
else
{
lean_object* x_424; lean_object* x_425; 
lean_dec(x_387);
x_424 = lean_ctor_get(x_389, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_389, 1);
lean_inc(x_425);
lean_dec(x_389);
x_252 = x_424;
x_253 = x_425;
goto block_292;
}
}
block_251:
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_213, 2);
lean_inc(x_214);
x_215 = !lean_is_exclusive(x_212);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_212, 0);
lean_dec(x_216);
x_217 = !lean_is_exclusive(x_213);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_213, 2);
lean_dec(x_218);
x_219 = !lean_is_exclusive(x_214);
if (x_219 == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_214, 2);
lean_dec(x_220);
lean_ctor_set(x_214, 2, x_210);
x_40 = x_211;
x_41 = x_212;
goto block_56;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_214, 0);
x_222 = lean_ctor_get(x_214, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_214);
x_223 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_210);
lean_ctor_set(x_213, 2, x_223);
x_40 = x_211;
x_41 = x_212;
goto block_56;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_224 = lean_ctor_get(x_213, 0);
x_225 = lean_ctor_get(x_213, 1);
x_226 = lean_ctor_get(x_213, 3);
x_227 = lean_ctor_get(x_213, 4);
x_228 = lean_ctor_get(x_213, 5);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_213);
x_229 = lean_ctor_get(x_214, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_214, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_231 = x_214;
} else {
 lean_dec_ref(x_214);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 3, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
lean_ctor_set(x_232, 2, x_210);
x_233 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_233, 0, x_224);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_232);
lean_ctor_set(x_233, 3, x_226);
lean_ctor_set(x_233, 4, x_227);
lean_ctor_set(x_233, 5, x_228);
lean_ctor_set(x_212, 0, x_233);
x_40 = x_211;
x_41 = x_212;
goto block_56;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_234 = lean_ctor_get(x_212, 1);
x_235 = lean_ctor_get(x_212, 2);
x_236 = lean_ctor_get(x_212, 3);
x_237 = lean_ctor_get(x_212, 4);
x_238 = lean_ctor_get(x_212, 5);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_212);
x_239 = lean_ctor_get(x_213, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_213, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_213, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_213, 4);
lean_inc(x_242);
x_243 = lean_ctor_get(x_213, 5);
lean_inc(x_243);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 x_244 = x_213;
} else {
 lean_dec_ref(x_213);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_214, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_214, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_247 = x_214;
} else {
 lean_dec_ref(x_214);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 3, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
lean_ctor_set(x_248, 2, x_210);
if (lean_is_scalar(x_244)) {
 x_249 = lean_alloc_ctor(0, 6, 0);
} else {
 x_249 = x_244;
}
lean_ctor_set(x_249, 0, x_239);
lean_ctor_set(x_249, 1, x_240);
lean_ctor_set(x_249, 2, x_248);
lean_ctor_set(x_249, 3, x_241);
lean_ctor_set(x_249, 4, x_242);
lean_ctor_set(x_249, 5, x_243);
x_250 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_234);
lean_ctor_set(x_250, 2, x_235);
lean_ctor_set(x_250, 3, x_236);
lean_ctor_set(x_250, 4, x_237);
lean_ctor_set(x_250, 5, x_238);
x_40 = x_211;
x_41 = x_250;
goto block_56;
}
}
block_292:
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_254, 2);
lean_inc(x_255);
x_256 = !lean_is_exclusive(x_253);
if (x_256 == 0)
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_ctor_get(x_253, 0);
lean_dec(x_257);
x_258 = !lean_is_exclusive(x_254);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_254, 2);
lean_dec(x_259);
x_260 = !lean_is_exclusive(x_255);
if (x_260 == 0)
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_255, 2);
lean_dec(x_261);
lean_ctor_set(x_255, 2, x_210);
x_23 = x_252;
x_24 = x_253;
goto block_39;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_255, 0);
x_263 = lean_ctor_get(x_255, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_255);
x_264 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_210);
lean_ctor_set(x_254, 2, x_264);
x_23 = x_252;
x_24 = x_253;
goto block_39;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_265 = lean_ctor_get(x_254, 0);
x_266 = lean_ctor_get(x_254, 1);
x_267 = lean_ctor_get(x_254, 3);
x_268 = lean_ctor_get(x_254, 4);
x_269 = lean_ctor_get(x_254, 5);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_254);
x_270 = lean_ctor_get(x_255, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_255, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_272 = x_255;
} else {
 lean_dec_ref(x_255);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(0, 3, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
lean_ctor_set(x_273, 2, x_210);
x_274 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_274, 0, x_265);
lean_ctor_set(x_274, 1, x_266);
lean_ctor_set(x_274, 2, x_273);
lean_ctor_set(x_274, 3, x_267);
lean_ctor_set(x_274, 4, x_268);
lean_ctor_set(x_274, 5, x_269);
lean_ctor_set(x_253, 0, x_274);
x_23 = x_252;
x_24 = x_253;
goto block_39;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_275 = lean_ctor_get(x_253, 1);
x_276 = lean_ctor_get(x_253, 2);
x_277 = lean_ctor_get(x_253, 3);
x_278 = lean_ctor_get(x_253, 4);
x_279 = lean_ctor_get(x_253, 5);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_253);
x_280 = lean_ctor_get(x_254, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_254, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_254, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_254, 4);
lean_inc(x_283);
x_284 = lean_ctor_get(x_254, 5);
lean_inc(x_284);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 lean_ctor_release(x_254, 3);
 lean_ctor_release(x_254, 4);
 lean_ctor_release(x_254, 5);
 x_285 = x_254;
} else {
 lean_dec_ref(x_254);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_255, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_255, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 x_288 = x_255;
} else {
 lean_dec_ref(x_255);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 3, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set(x_289, 2, x_210);
if (lean_is_scalar(x_285)) {
 x_290 = lean_alloc_ctor(0, 6, 0);
} else {
 x_290 = x_285;
}
lean_ctor_set(x_290, 0, x_280);
lean_ctor_set(x_290, 1, x_281);
lean_ctor_set(x_290, 2, x_289);
lean_ctor_set(x_290, 3, x_282);
lean_ctor_set(x_290, 4, x_283);
lean_ctor_set(x_290, 5, x_284);
x_291 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_275);
lean_ctor_set(x_291, 2, x_276);
lean_ctor_set(x_291, 3, x_277);
lean_ctor_set(x_291, 4, x_278);
lean_ctor_set(x_291, 5, x_279);
x_23 = x_252;
x_24 = x_291;
goto block_39;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; 
lean_dec(x_64);
lean_dec(x_5);
x_426 = lean_ctor_get(x_68, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_68, 1);
lean_inc(x_427);
lean_dec(x_68);
x_23 = x_426;
x_24 = x_427;
goto block_39;
}
block_20:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_12, x_2, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
block_39:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = l_Lean_Elab_Term_getTraceState___rarg(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_30 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__2(x_3, x_28, x_29, x_7, x_27);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Elab_Term_setTraceState(x_21, x_7, x_31);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_23);
x_35 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_32);
x_13 = x_35;
goto block_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_37);
x_13 = x_38;
goto block_20;
}
}
block_56:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = l_Lean_Elab_Term_getTraceState___rarg(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_47 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__3(x_3, x_45, x_46, x_7, x_44);
lean_dec(x_45);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Elab_Term_setTraceState(x_21, x_7, x_48);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_40);
x_52 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_49);
x_13 = x_52;
goto block_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_54);
x_13 = x_55;
goto block_20;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariable___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabVariable(x_1, x_2, x_3);
lean_dec(x_2);
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
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 3);
lean_dec(x_6);
x_7 = l_Lean_Elab_Command_modifyScope___closed__1;
x_8 = l_unreachable_x21___rarg(x_7);
lean_ctor_set(x_3, 3, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l_Lean_Elab_Command_modifyScope___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_3, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_19, 6);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_26, x_25);
lean_ctor_set(x_19, 6, x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
x_32 = lean_ctor_get(x_19, 2);
x_33 = lean_ctor_get(x_19, 3);
x_34 = lean_ctor_get(x_19, 4);
x_35 = lean_ctor_get(x_19, 5);
x_36 = lean_ctor_get(x_19, 6);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_37, x_36);
x_39 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_38);
lean_ctor_set(x_4, 0, x_39);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_dec(x_4);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_19, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_19, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_19, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_19, 6);
lean_inc(x_49);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_50 = x_19;
} else {
 lean_dec_ref(x_19);
 x_50 = lean_box(0);
}
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_51, x_49);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 7, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_46);
lean_ctor_set(x_53, 4, x_47);
lean_ctor_set(x_53, 5, x_48);
lean_ctor_set(x_53, 6, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_3, 3, x_54);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
x_59 = lean_ctor_get(x_3, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_61 = x_4;
} else {
 lean_dec_ref(x_4);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_19, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_19, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_19, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_19, 6);
lean_inc(x_68);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 x_69 = x_19;
} else {
 lean_dec_ref(x_19);
 x_69 = lean_box(0);
}
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_70, x_68);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 7, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_64);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_67);
lean_ctor_set(x_72, 6, x_71);
if (lean_is_scalar(x_61)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_61;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_60);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_57);
lean_ctor_set(x_74, 1, x_58);
lean_ctor_set(x_74, 2, x_59);
lean_ctor_set(x_74, 3, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Command_elabVariables(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_41; lean_object* x_42; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = l___private_Init_Lean_Elab_Command_3__getVarDecls(x_3);
x_7 = l___private_Init_Lean_Elab_Command_1__mkTermContext(x_2, x_3);
x_8 = l___private_Init_Lean_Elab_Command_2__mkTermState(x_3);
x_9 = l_Lean_Elab_Term_getTraceState___rarg(x_8);
x_10 = l_Lean_stxInh;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_array_get(x_10, x_4, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_58 = l_Lean_TraceState_Inhabited___closed__1;
x_59 = l_Lean_Elab_Term_setTraceState(x_58, x_7, x_23);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Elab_Term_getLCtx(x_7, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Elab_Term_getLocalInsts(x_7, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_empty___closed__1;
lean_inc(x_7);
lean_inc(x_65);
x_69 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_6, x_67, x_68, x_62, x_65, x_7, x_66);
lean_dec(x_6);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_array_get_size(x_65);
lean_dec(x_65);
x_76 = lean_array_get_size(x_74);
x_77 = lean_nat_dec_lt(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_7, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_7, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_7, 5);
lean_inc(x_80);
x_81 = lean_ctor_get(x_7, 6);
lean_inc(x_81);
x_82 = lean_ctor_get(x_7, 8);
lean_inc(x_82);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_84 = lean_ctor_get(x_78, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_dec(x_85);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set(x_78, 1, x_73);
x_86 = lean_ctor_get(x_2, 0);
x_87 = lean_ctor_get(x_2, 1);
x_88 = lean_box(0);
x_89 = 1;
lean_inc(x_87);
lean_inc(x_86);
x_90 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_87);
lean_ctor_set(x_90, 3, x_5);
lean_ctor_set(x_90, 4, x_79);
lean_ctor_set(x_90, 5, x_80);
lean_ctor_set(x_90, 6, x_81);
lean_ctor_set(x_90, 7, x_88);
lean_ctor_set(x_90, 8, x_82);
lean_ctor_set_uint8(x_90, sizeof(void*)*9, x_89);
x_91 = l_Lean_Elab_Term_getLCtx(x_90, x_72);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Elab_Term_getLocalInsts(x_90, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_95);
x_97 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_13, x_67, x_68, x_92, x_95, x_90, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_array_get_size(x_95);
lean_dec(x_95);
x_103 = lean_array_get_size(x_101);
lean_dec(x_101);
x_104 = lean_nat_dec_lt(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_box(0);
x_41 = x_105;
x_42 = x_100;
goto block_57;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 2);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_100);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 2);
lean_inc(x_112);
x_113 = !lean_is_exclusive(x_110);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_111, 2);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_112);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_112, 2);
lean_dec(x_118);
lean_ctor_set(x_112, 2, x_108);
x_119 = lean_box(0);
x_41 = x_119;
x_42 = x_110;
goto block_57;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_112, 0);
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_112);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_122, 2, x_108);
lean_ctor_set(x_111, 2, x_122);
x_123 = lean_box(0);
x_41 = x_123;
x_42 = x_110;
goto block_57;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_ctor_get(x_111, 0);
x_125 = lean_ctor_get(x_111, 1);
x_126 = lean_ctor_get(x_111, 3);
x_127 = lean_ctor_get(x_111, 4);
x_128 = lean_ctor_get(x_111, 5);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_111);
x_129 = lean_ctor_get(x_112, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_112, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 x_131 = x_112;
} else {
 lean_dec_ref(x_112);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_108);
x_133 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_126);
lean_ctor_set(x_133, 4, x_127);
lean_ctor_set(x_133, 5, x_128);
lean_ctor_set(x_110, 0, x_133);
x_134 = lean_box(0);
x_41 = x_134;
x_42 = x_110;
goto block_57;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_135 = lean_ctor_get(x_110, 1);
x_136 = lean_ctor_get(x_110, 2);
x_137 = lean_ctor_get(x_110, 3);
x_138 = lean_ctor_get(x_110, 4);
x_139 = lean_ctor_get(x_110, 5);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_110);
x_140 = lean_ctor_get(x_111, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_111, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_111, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_111, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_111, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 lean_ctor_release(x_111, 5);
 x_145 = x_111;
} else {
 lean_dec_ref(x_111);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_112, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_112, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 x_148 = x_112;
} else {
 lean_dec_ref(x_112);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 3, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_108);
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(0, 6, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_140);
lean_ctor_set(x_150, 1, x_141);
lean_ctor_set(x_150, 2, x_149);
lean_ctor_set(x_150, 3, x_142);
lean_ctor_set(x_150, 4, x_143);
lean_ctor_set(x_150, 5, x_144);
x_151 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_135);
lean_ctor_set(x_151, 2, x_136);
lean_ctor_set(x_151, 3, x_137);
lean_ctor_set(x_151, 4, x_138);
lean_ctor_set(x_151, 5, x_139);
x_152 = lean_box(0);
x_41 = x_152;
x_42 = x_151;
goto block_57;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_95);
x_153 = lean_ctor_get(x_97, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_97, 1);
lean_inc(x_154);
lean_dec(x_97);
x_24 = x_153;
x_25 = x_154;
goto block_40;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_155 = lean_ctor_get(x_78, 0);
lean_inc(x_155);
lean_dec(x_78);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_73);
lean_ctor_set(x_156, 2, x_74);
x_157 = lean_ctor_get(x_2, 0);
x_158 = lean_ctor_get(x_2, 1);
x_159 = lean_box(0);
x_160 = 1;
lean_inc(x_158);
lean_inc(x_157);
x_161 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_157);
lean_ctor_set(x_161, 2, x_158);
lean_ctor_set(x_161, 3, x_5);
lean_ctor_set(x_161, 4, x_79);
lean_ctor_set(x_161, 5, x_80);
lean_ctor_set(x_161, 6, x_81);
lean_ctor_set(x_161, 7, x_159);
lean_ctor_set(x_161, 8, x_82);
lean_ctor_set_uint8(x_161, sizeof(void*)*9, x_160);
x_162 = l_Lean_Elab_Term_getLCtx(x_161, x_72);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Elab_Term_getLocalInsts(x_161, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_166);
x_168 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_13, x_67, x_68, x_163, x_166, x_161, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_array_get_size(x_166);
lean_dec(x_166);
x_174 = lean_array_get_size(x_172);
lean_dec(x_172);
x_175 = lean_nat_dec_lt(x_173, x_174);
lean_dec(x_174);
lean_dec(x_173);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_box(0);
x_41 = x_176;
x_42 = x_171;
goto block_57;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_177, 2);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_ctor_get(x_178, 2);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_171);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_181, 5);
lean_inc(x_188);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 lean_ctor_release(x_181, 4);
 lean_ctor_release(x_181, 5);
 x_189 = x_181;
} else {
 lean_dec_ref(x_181);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_182, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_182, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_182, 4);
lean_inc(x_193);
x_194 = lean_ctor_get(x_182, 5);
lean_inc(x_194);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 lean_ctor_release(x_182, 5);
 x_195 = x_182;
} else {
 lean_dec_ref(x_182);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_183, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_183, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 x_198 = x_183;
} else {
 lean_dec_ref(x_183);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 3, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_179);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_199);
lean_ctor_set(x_200, 3, x_192);
lean_ctor_set(x_200, 4, x_193);
lean_ctor_set(x_200, 5, x_194);
if (lean_is_scalar(x_189)) {
 x_201 = lean_alloc_ctor(0, 6, 0);
} else {
 x_201 = x_189;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_184);
lean_ctor_set(x_201, 2, x_185);
lean_ctor_set(x_201, 3, x_186);
lean_ctor_set(x_201, 4, x_187);
lean_ctor_set(x_201, 5, x_188);
x_202 = lean_box(0);
x_41 = x_202;
x_42 = x_201;
goto block_57;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_166);
x_203 = lean_ctor_get(x_168, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_168, 1);
lean_inc(x_204);
lean_dec(x_168);
x_24 = x_203;
x_25 = x_204;
goto block_40;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_249; lean_object* x_250; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_205 = lean_ctor_get(x_72, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_205, 2);
lean_inc(x_206);
lean_dec(x_205);
x_207 = lean_ctor_get(x_206, 2);
lean_inc(x_207);
lean_dec(x_206);
x_290 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_72);
x_291 = lean_ctor_get(x_7, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_7, 4);
lean_inc(x_293);
x_294 = lean_ctor_get(x_7, 5);
lean_inc(x_294);
x_295 = lean_ctor_get(x_7, 6);
lean_inc(x_295);
x_296 = lean_ctor_get(x_7, 8);
lean_inc(x_296);
x_297 = !lean_is_exclusive(x_291);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_298 = lean_ctor_get(x_291, 2);
lean_dec(x_298);
x_299 = lean_ctor_get(x_291, 1);
lean_dec(x_299);
lean_ctor_set(x_291, 2, x_74);
lean_ctor_set(x_291, 1, x_73);
x_300 = lean_ctor_get(x_2, 0);
x_301 = lean_ctor_get(x_2, 1);
x_302 = lean_box(0);
x_303 = 1;
lean_inc(x_301);
lean_inc(x_300);
x_304 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_304, 0, x_291);
lean_ctor_set(x_304, 1, x_300);
lean_ctor_set(x_304, 2, x_301);
lean_ctor_set(x_304, 3, x_5);
lean_ctor_set(x_304, 4, x_293);
lean_ctor_set(x_304, 5, x_294);
lean_ctor_set(x_304, 6, x_295);
lean_ctor_set(x_304, 7, x_302);
lean_ctor_set(x_304, 8, x_296);
lean_ctor_set_uint8(x_304, sizeof(void*)*9, x_303);
x_305 = l_Lean_Elab_Term_getLCtx(x_304, x_292);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = l_Lean_Elab_Term_getLocalInsts(x_304, x_307);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
lean_inc(x_309);
x_311 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_13, x_67, x_68, x_306, x_309, x_304, x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_array_get_size(x_309);
lean_dec(x_309);
x_317 = lean_array_get_size(x_315);
lean_dec(x_315);
x_318 = lean_nat_dec_lt(x_316, x_317);
lean_dec(x_317);
lean_dec(x_316);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_box(0);
x_208 = x_319;
x_209 = x_314;
goto block_248;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_320 = lean_ctor_get(x_314, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_320, 2);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_ctor_get(x_321, 2);
lean_inc(x_322);
lean_dec(x_321);
x_323 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_314);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
lean_dec(x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 2);
lean_inc(x_326);
x_327 = !lean_is_exclusive(x_324);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_ctor_get(x_324, 0);
lean_dec(x_328);
x_329 = !lean_is_exclusive(x_325);
if (x_329 == 0)
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_325, 2);
lean_dec(x_330);
x_331 = !lean_is_exclusive(x_326);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_326, 2);
lean_dec(x_332);
lean_ctor_set(x_326, 2, x_322);
x_333 = lean_box(0);
x_208 = x_333;
x_209 = x_324;
goto block_248;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_ctor_get(x_326, 0);
x_335 = lean_ctor_get(x_326, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_326);
x_336 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
lean_ctor_set(x_336, 2, x_322);
lean_ctor_set(x_325, 2, x_336);
x_337 = lean_box(0);
x_208 = x_337;
x_209 = x_324;
goto block_248;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_338 = lean_ctor_get(x_325, 0);
x_339 = lean_ctor_get(x_325, 1);
x_340 = lean_ctor_get(x_325, 3);
x_341 = lean_ctor_get(x_325, 4);
x_342 = lean_ctor_get(x_325, 5);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_325);
x_343 = lean_ctor_get(x_326, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_326, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 x_345 = x_326;
} else {
 lean_dec_ref(x_326);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 3, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
lean_ctor_set(x_346, 2, x_322);
x_347 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_347, 0, x_338);
lean_ctor_set(x_347, 1, x_339);
lean_ctor_set(x_347, 2, x_346);
lean_ctor_set(x_347, 3, x_340);
lean_ctor_set(x_347, 4, x_341);
lean_ctor_set(x_347, 5, x_342);
lean_ctor_set(x_324, 0, x_347);
x_348 = lean_box(0);
x_208 = x_348;
x_209 = x_324;
goto block_248;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_349 = lean_ctor_get(x_324, 1);
x_350 = lean_ctor_get(x_324, 2);
x_351 = lean_ctor_get(x_324, 3);
x_352 = lean_ctor_get(x_324, 4);
x_353 = lean_ctor_get(x_324, 5);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_324);
x_354 = lean_ctor_get(x_325, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_325, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_325, 3);
lean_inc(x_356);
x_357 = lean_ctor_get(x_325, 4);
lean_inc(x_357);
x_358 = lean_ctor_get(x_325, 5);
lean_inc(x_358);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 lean_ctor_release(x_325, 4);
 lean_ctor_release(x_325, 5);
 x_359 = x_325;
} else {
 lean_dec_ref(x_325);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_326, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 x_362 = x_326;
} else {
 lean_dec_ref(x_326);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 3, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
lean_ctor_set(x_363, 2, x_322);
if (lean_is_scalar(x_359)) {
 x_364 = lean_alloc_ctor(0, 6, 0);
} else {
 x_364 = x_359;
}
lean_ctor_set(x_364, 0, x_354);
lean_ctor_set(x_364, 1, x_355);
lean_ctor_set(x_364, 2, x_363);
lean_ctor_set(x_364, 3, x_356);
lean_ctor_set(x_364, 4, x_357);
lean_ctor_set(x_364, 5, x_358);
x_365 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_349);
lean_ctor_set(x_365, 2, x_350);
lean_ctor_set(x_365, 3, x_351);
lean_ctor_set(x_365, 4, x_352);
lean_ctor_set(x_365, 5, x_353);
x_366 = lean_box(0);
x_208 = x_366;
x_209 = x_365;
goto block_248;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_309);
x_367 = lean_ctor_get(x_311, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_311, 1);
lean_inc(x_368);
lean_dec(x_311);
x_249 = x_367;
x_250 = x_368;
goto block_289;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_369 = lean_ctor_get(x_291, 0);
lean_inc(x_369);
lean_dec(x_291);
x_370 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_73);
lean_ctor_set(x_370, 2, x_74);
x_371 = lean_ctor_get(x_2, 0);
x_372 = lean_ctor_get(x_2, 1);
x_373 = lean_box(0);
x_374 = 1;
lean_inc(x_372);
lean_inc(x_371);
x_375 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_375, 0, x_370);
lean_ctor_set(x_375, 1, x_371);
lean_ctor_set(x_375, 2, x_372);
lean_ctor_set(x_375, 3, x_5);
lean_ctor_set(x_375, 4, x_293);
lean_ctor_set(x_375, 5, x_294);
lean_ctor_set(x_375, 6, x_295);
lean_ctor_set(x_375, 7, x_373);
lean_ctor_set(x_375, 8, x_296);
lean_ctor_set_uint8(x_375, sizeof(void*)*9, x_374);
x_376 = l_Lean_Elab_Term_getLCtx(x_375, x_292);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = l_Lean_Elab_Term_getLocalInsts(x_375, x_378);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
lean_inc(x_380);
x_382 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_13, x_67, x_68, x_377, x_380, x_375, x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec(x_383);
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
lean_dec(x_382);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_array_get_size(x_380);
lean_dec(x_380);
x_388 = lean_array_get_size(x_386);
lean_dec(x_386);
x_389 = lean_nat_dec_lt(x_387, x_388);
lean_dec(x_388);
lean_dec(x_387);
if (x_389 == 0)
{
lean_object* x_390; 
x_390 = lean_box(0);
x_208 = x_390;
x_209 = x_385;
goto block_248;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_391 = lean_ctor_get(x_385, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_391, 2);
lean_inc(x_392);
lean_dec(x_391);
x_393 = lean_ctor_get(x_392, 2);
lean_inc(x_393);
lean_dec(x_392);
x_394 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_385);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_396, 2);
lean_inc(x_397);
x_398 = lean_ctor_get(x_395, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_395, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_395, 3);
lean_inc(x_400);
x_401 = lean_ctor_get(x_395, 4);
lean_inc(x_401);
x_402 = lean_ctor_get(x_395, 5);
lean_inc(x_402);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 lean_ctor_release(x_395, 2);
 lean_ctor_release(x_395, 3);
 lean_ctor_release(x_395, 4);
 lean_ctor_release(x_395, 5);
 x_403 = x_395;
} else {
 lean_dec_ref(x_395);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_396, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_396, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_396, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_396, 4);
lean_inc(x_407);
x_408 = lean_ctor_get(x_396, 5);
lean_inc(x_408);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 lean_ctor_release(x_396, 4);
 lean_ctor_release(x_396, 5);
 x_409 = x_396;
} else {
 lean_dec_ref(x_396);
 x_409 = lean_box(0);
}
x_410 = lean_ctor_get(x_397, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_397, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 lean_ctor_release(x_397, 2);
 x_412 = x_397;
} else {
 lean_dec_ref(x_397);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(0, 3, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
lean_ctor_set(x_413, 2, x_393);
if (lean_is_scalar(x_409)) {
 x_414 = lean_alloc_ctor(0, 6, 0);
} else {
 x_414 = x_409;
}
lean_ctor_set(x_414, 0, x_404);
lean_ctor_set(x_414, 1, x_405);
lean_ctor_set(x_414, 2, x_413);
lean_ctor_set(x_414, 3, x_406);
lean_ctor_set(x_414, 4, x_407);
lean_ctor_set(x_414, 5, x_408);
if (lean_is_scalar(x_403)) {
 x_415 = lean_alloc_ctor(0, 6, 0);
} else {
 x_415 = x_403;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_398);
lean_ctor_set(x_415, 2, x_399);
lean_ctor_set(x_415, 3, x_400);
lean_ctor_set(x_415, 4, x_401);
lean_ctor_set(x_415, 5, x_402);
x_416 = lean_box(0);
x_208 = x_416;
x_209 = x_415;
goto block_248;
}
}
else
{
lean_object* x_417; lean_object* x_418; 
lean_dec(x_380);
x_417 = lean_ctor_get(x_382, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_382, 1);
lean_inc(x_418);
lean_dec(x_382);
x_249 = x_417;
x_250 = x_418;
goto block_289;
}
}
block_248:
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_210, 2);
lean_inc(x_211);
x_212 = !lean_is_exclusive(x_209);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_209, 0);
lean_dec(x_213);
x_214 = !lean_is_exclusive(x_210);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_210, 2);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_211);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_211, 2);
lean_dec(x_217);
lean_ctor_set(x_211, 2, x_207);
x_41 = x_208;
x_42 = x_209;
goto block_57;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_211, 0);
x_219 = lean_ctor_get(x_211, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_211);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_220, 2, x_207);
lean_ctor_set(x_210, 2, x_220);
x_41 = x_208;
x_42 = x_209;
goto block_57;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_221 = lean_ctor_get(x_210, 0);
x_222 = lean_ctor_get(x_210, 1);
x_223 = lean_ctor_get(x_210, 3);
x_224 = lean_ctor_get(x_210, 4);
x_225 = lean_ctor_get(x_210, 5);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_210);
x_226 = lean_ctor_get(x_211, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_211, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 x_228 = x_211;
} else {
 lean_dec_ref(x_211);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 3, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
lean_ctor_set(x_229, 2, x_207);
x_230 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_222);
lean_ctor_set(x_230, 2, x_229);
lean_ctor_set(x_230, 3, x_223);
lean_ctor_set(x_230, 4, x_224);
lean_ctor_set(x_230, 5, x_225);
lean_ctor_set(x_209, 0, x_230);
x_41 = x_208;
x_42 = x_209;
goto block_57;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_231 = lean_ctor_get(x_209, 1);
x_232 = lean_ctor_get(x_209, 2);
x_233 = lean_ctor_get(x_209, 3);
x_234 = lean_ctor_get(x_209, 4);
x_235 = lean_ctor_get(x_209, 5);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_209);
x_236 = lean_ctor_get(x_210, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_210, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_210, 3);
lean_inc(x_238);
x_239 = lean_ctor_get(x_210, 4);
lean_inc(x_239);
x_240 = lean_ctor_get(x_210, 5);
lean_inc(x_240);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 lean_ctor_release(x_210, 5);
 x_241 = x_210;
} else {
 lean_dec_ref(x_210);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_211, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_211, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 x_244 = x_211;
} else {
 lean_dec_ref(x_211);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 3, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
lean_ctor_set(x_245, 2, x_207);
if (lean_is_scalar(x_241)) {
 x_246 = lean_alloc_ctor(0, 6, 0);
} else {
 x_246 = x_241;
}
lean_ctor_set(x_246, 0, x_236);
lean_ctor_set(x_246, 1, x_237);
lean_ctor_set(x_246, 2, x_245);
lean_ctor_set(x_246, 3, x_238);
lean_ctor_set(x_246, 4, x_239);
lean_ctor_set(x_246, 5, x_240);
x_247 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_231);
lean_ctor_set(x_247, 2, x_232);
lean_ctor_set(x_247, 3, x_233);
lean_ctor_set(x_247, 4, x_234);
lean_ctor_set(x_247, 5, x_235);
x_41 = x_208;
x_42 = x_247;
goto block_57;
}
}
block_289:
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_251, 2);
lean_inc(x_252);
x_253 = !lean_is_exclusive(x_250);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_250, 0);
lean_dec(x_254);
x_255 = !lean_is_exclusive(x_251);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_251, 2);
lean_dec(x_256);
x_257 = !lean_is_exclusive(x_252);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_252, 2);
lean_dec(x_258);
lean_ctor_set(x_252, 2, x_207);
x_24 = x_249;
x_25 = x_250;
goto block_40;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_252, 0);
x_260 = lean_ctor_get(x_252, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_252);
x_261 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
lean_ctor_set(x_261, 2, x_207);
lean_ctor_set(x_251, 2, x_261);
x_24 = x_249;
x_25 = x_250;
goto block_40;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_262 = lean_ctor_get(x_251, 0);
x_263 = lean_ctor_get(x_251, 1);
x_264 = lean_ctor_get(x_251, 3);
x_265 = lean_ctor_get(x_251, 4);
x_266 = lean_ctor_get(x_251, 5);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_251);
x_267 = lean_ctor_get(x_252, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_252, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_269 = x_252;
} else {
 lean_dec_ref(x_252);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(0, 3, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
lean_ctor_set(x_270, 2, x_207);
x_271 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_271, 0, x_262);
lean_ctor_set(x_271, 1, x_263);
lean_ctor_set(x_271, 2, x_270);
lean_ctor_set(x_271, 3, x_264);
lean_ctor_set(x_271, 4, x_265);
lean_ctor_set(x_271, 5, x_266);
lean_ctor_set(x_250, 0, x_271);
x_24 = x_249;
x_25 = x_250;
goto block_40;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_272 = lean_ctor_get(x_250, 1);
x_273 = lean_ctor_get(x_250, 2);
x_274 = lean_ctor_get(x_250, 3);
x_275 = lean_ctor_get(x_250, 4);
x_276 = lean_ctor_get(x_250, 5);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_250);
x_277 = lean_ctor_get(x_251, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_251, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_251, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_251, 4);
lean_inc(x_280);
x_281 = lean_ctor_get(x_251, 5);
lean_inc(x_281);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 lean_ctor_release(x_251, 5);
 x_282 = x_251;
} else {
 lean_dec_ref(x_251);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_252, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_252, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 lean_ctor_release(x_252, 2);
 x_285 = x_252;
} else {
 lean_dec_ref(x_252);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(0, 3, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
lean_ctor_set(x_286, 2, x_207);
if (lean_is_scalar(x_282)) {
 x_287 = lean_alloc_ctor(0, 6, 0);
} else {
 x_287 = x_282;
}
lean_ctor_set(x_287, 0, x_277);
lean_ctor_set(x_287, 1, x_278);
lean_ctor_set(x_287, 2, x_286);
lean_ctor_set(x_287, 3, x_279);
lean_ctor_set(x_287, 4, x_280);
lean_ctor_set(x_287, 5, x_281);
x_288 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_272);
lean_ctor_set(x_288, 2, x_273);
lean_ctor_set(x_288, 3, x_274);
lean_ctor_set(x_288, 4, x_275);
lean_ctor_set(x_288, 5, x_276);
x_24 = x_249;
x_25 = x_288;
goto block_40;
}
}
}
}
else
{
lean_object* x_419; lean_object* x_420; 
lean_dec(x_65);
lean_dec(x_5);
x_419 = lean_ctor_get(x_69, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_69, 1);
lean_inc(x_420);
lean_dec(x_69);
x_24 = x_419;
x_25 = x_420;
goto block_40;
}
block_21:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_13, x_2, x_15);
lean_dec(x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
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
block_40:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = l_Lean_Elab_Term_getTraceState___rarg(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_31 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__2(x_3, x_29, x_30, x_7, x_28);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Elab_Term_setTraceState(x_22, x_7, x_32);
lean_dec(x_7);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_24);
x_36 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_33);
x_14 = x_36;
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_38);
x_14 = x_39;
goto block_21;
}
}
block_57:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = l_Lean_Elab_Term_getTraceState___rarg(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_48 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__3(x_3, x_46, x_47, x_7, x_45);
lean_dec(x_46);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Elab_Term_setTraceState(x_22, x_7, x_49);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_41);
x_53 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_50);
x_14 = x_53;
goto block_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_55);
x_14 = x_56;
goto block_21;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabVariables___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabVariables(x_1, x_2, x_3);
lean_dec(x_2);
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
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = 0;
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_6, x_14, x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_3 = x_13;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Command_elabCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_33; lean_object* x_34; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l___private_Init_Lean_Elab_Command_3__getVarDecls(x_3);
x_8 = l___private_Init_Lean_Elab_Command_1__mkTermContext(x_2, x_3);
x_9 = l___private_Init_Lean_Elab_Command_2__mkTermState(x_3);
x_10 = l_Lean_Elab_Term_getTraceState___rarg(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_stxInh;
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_array_get(x_13, x_4, x_14);
x_50 = l_Lean_TraceState_Inhabited___closed__1;
x_51 = l_Lean_Elab_Term_setTraceState(x_50, x_8, x_12);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Elab_Term_getLCtx(x_8, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_getLocalInsts(x_8, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_57);
x_61 = l___private_Init_Lean_Elab_Term_24__elabBindersAux___main(x_7, x_59, x_60, x_54, x_57, x_8, x_58);
lean_dec(x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_array_get_size(x_57);
lean_dec(x_57);
x_68 = lean_array_get_size(x_66);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_8, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_8, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_8, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_8, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_8, 8);
lean_inc(x_74);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_70, 2);
lean_dec(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_dec(x_77);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 1, x_65);
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 1);
x_80 = lean_box(0);
x_81 = 1;
lean_inc(x_79);
lean_inc(x_78);
x_82 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_6);
lean_ctor_set(x_82, 4, x_71);
lean_ctor_set(x_82, 5, x_72);
lean_ctor_set(x_82, 6, x_73);
lean_ctor_set(x_82, 7, x_80);
lean_ctor_set(x_82, 8, x_74);
lean_ctor_set_uint8(x_82, sizeof(void*)*9, x_81);
x_83 = 0;
lean_inc(x_82);
x_84 = l_Lean_Elab_Term_elabTerm(x_15, x_5, x_83, x_82, x_64);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(0);
lean_inc(x_82);
x_88 = l___private_Init_Lean_Elab_Term_18__synthesizeSyntheticMVarsAux___main(x_83, x_87, x_82, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_82);
lean_inc(x_85);
x_90 = l_Lean_Elab_Term_inferType(x_1, x_85, x_82, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_82);
x_93 = l_Lean_Elab_Term_instantiateMVars(x_1, x_85, x_82, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_82);
x_96 = l_Lean_Elab_Term_instantiateMVars(x_1, x_91, x_82, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_100 = l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__8;
x_101 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_103 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = 0;
x_105 = l_Lean_Elab_log___at___private_Init_Lean_Elab_Term_17__reportStuckSyntheticMVars___spec__1(x_1, x_104, x_103, x_82, x_98);
lean_dec(x_82);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_33 = x_87;
x_34 = x_106;
goto block_49;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_85);
lean_dec(x_82);
x_107 = lean_ctor_get(x_90, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_90, 1);
lean_inc(x_108);
lean_dec(x_90);
x_16 = x_107;
x_17 = x_108;
goto block_32;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_85);
lean_dec(x_82);
x_109 = lean_ctor_get(x_88, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_88, 1);
lean_inc(x_110);
lean_dec(x_88);
x_16 = x_109;
x_17 = x_110;
goto block_32;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_82);
x_111 = lean_ctor_get(x_84, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_84, 1);
lean_inc(x_112);
lean_dec(x_84);
x_16 = x_111;
x_17 = x_112;
goto block_32;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_70, 0);
lean_inc(x_113);
lean_dec(x_70);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_65);
lean_ctor_set(x_114, 2, x_66);
x_115 = lean_ctor_get(x_2, 0);
x_116 = lean_ctor_get(x_2, 1);
x_117 = lean_box(0);
x_118 = 1;
lean_inc(x_116);
lean_inc(x_115);
x_119 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
lean_ctor_set(x_119, 2, x_116);
lean_ctor_set(x_119, 3, x_6);
lean_ctor_set(x_119, 4, x_71);
lean_ctor_set(x_119, 5, x_72);
lean_ctor_set(x_119, 6, x_73);
lean_ctor_set(x_119, 7, x_117);
lean_ctor_set(x_119, 8, x_74);
lean_ctor_set_uint8(x_119, sizeof(void*)*9, x_118);
x_120 = 0;
lean_inc(x_119);
x_121 = l_Lean_Elab_Term_elabTerm(x_15, x_5, x_120, x_119, x_64);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_box(0);
lean_inc(x_119);
x_125 = l___private_Init_Lean_Elab_Term_18__synthesizeSyntheticMVarsAux___main(x_120, x_124, x_119, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
lean_inc(x_119);
lean_inc(x_122);
x_127 = l_Lean_Elab_Term_inferType(x_1, x_122, x_119, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_119);
x_130 = l_Lean_Elab_Term_instantiateMVars(x_1, x_122, x_119, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_119);
x_133 = l_Lean_Elab_Term_instantiateMVars(x_1, x_128, x_119, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_136, 0, x_131);
x_137 = l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__8;
x_138 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_139, 0, x_134);
x_140 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = 0;
x_142 = l_Lean_Elab_log___at___private_Init_Lean_Elab_Term_17__reportStuckSyntheticMVars___spec__1(x_1, x_141, x_140, x_119, x_135);
lean_dec(x_119);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_33 = x_124;
x_34 = x_143;
goto block_49;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_122);
lean_dec(x_119);
x_144 = lean_ctor_get(x_127, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_127, 1);
lean_inc(x_145);
lean_dec(x_127);
x_16 = x_144;
x_17 = x_145;
goto block_32;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_122);
lean_dec(x_119);
x_146 = lean_ctor_get(x_125, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_125, 1);
lean_inc(x_147);
lean_dec(x_125);
x_16 = x_146;
x_17 = x_147;
goto block_32;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_119);
x_148 = lean_ctor_get(x_121, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_121, 1);
lean_inc(x_149);
lean_dec(x_121);
x_16 = x_148;
x_17 = x_149;
goto block_32;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_150 = lean_ctor_get(x_64, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_150, 2);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_ctor_get(x_151, 2);
lean_inc(x_152);
lean_dec(x_151);
x_194 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_64);
x_195 = lean_ctor_get(x_8, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_8, 4);
lean_inc(x_197);
x_198 = lean_ctor_get(x_8, 5);
lean_inc(x_198);
x_199 = lean_ctor_get(x_8, 6);
lean_inc(x_199);
x_200 = lean_ctor_get(x_8, 8);
lean_inc(x_200);
x_201 = !lean_is_exclusive(x_195);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; 
x_202 = lean_ctor_get(x_195, 2);
lean_dec(x_202);
x_203 = lean_ctor_get(x_195, 1);
lean_dec(x_203);
lean_ctor_set(x_195, 2, x_66);
lean_ctor_set(x_195, 1, x_65);
x_204 = lean_ctor_get(x_2, 0);
x_205 = lean_ctor_get(x_2, 1);
x_206 = lean_box(0);
x_207 = 1;
lean_inc(x_205);
lean_inc(x_204);
x_208 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_208, 0, x_195);
lean_ctor_set(x_208, 1, x_204);
lean_ctor_set(x_208, 2, x_205);
lean_ctor_set(x_208, 3, x_6);
lean_ctor_set(x_208, 4, x_197);
lean_ctor_set(x_208, 5, x_198);
lean_ctor_set(x_208, 6, x_199);
lean_ctor_set(x_208, 7, x_206);
lean_ctor_set(x_208, 8, x_200);
lean_ctor_set_uint8(x_208, sizeof(void*)*9, x_207);
x_209 = 0;
lean_inc(x_208);
x_210 = l_Lean_Elab_Term_elabTerm(x_15, x_5, x_209, x_208, x_196);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_box(0);
lean_inc(x_208);
x_214 = l___private_Init_Lean_Elab_Term_18__synthesizeSyntheticMVarsAux___main(x_209, x_213, x_208, x_212);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
lean_inc(x_208);
lean_inc(x_211);
x_216 = l_Lean_Elab_Term_inferType(x_1, x_211, x_208, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_208);
x_219 = l_Lean_Elab_Term_instantiateMVars(x_1, x_211, x_208, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_208);
x_222 = l_Lean_Elab_Term_instantiateMVars(x_1, x_217, x_208, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_220);
x_226 = l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__8;
x_227 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_228, 0, x_223);
x_229 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = 0;
x_231 = l_Lean_Elab_log___at___private_Init_Lean_Elab_Term_17__reportStuckSyntheticMVars___spec__1(x_1, x_230, x_229, x_208, x_224);
lean_dec(x_208);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 2);
lean_inc(x_234);
x_235 = !lean_is_exclusive(x_232);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_ctor_get(x_232, 0);
lean_dec(x_236);
x_237 = !lean_is_exclusive(x_233);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_233, 2);
lean_dec(x_238);
x_239 = !lean_is_exclusive(x_234);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_234, 2);
lean_dec(x_240);
lean_ctor_set(x_234, 2, x_152);
x_33 = x_213;
x_34 = x_232;
goto block_49;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_234, 0);
x_242 = lean_ctor_get(x_234, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_234);
x_243 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_243, 2, x_152);
lean_ctor_set(x_233, 2, x_243);
x_33 = x_213;
x_34 = x_232;
goto block_49;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_244 = lean_ctor_get(x_233, 0);
x_245 = lean_ctor_get(x_233, 1);
x_246 = lean_ctor_get(x_233, 3);
x_247 = lean_ctor_get(x_233, 4);
x_248 = lean_ctor_get(x_233, 5);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_233);
x_249 = lean_ctor_get(x_234, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_234, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 x_251 = x_234;
} else {
 lean_dec_ref(x_234);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(0, 3, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
lean_ctor_set(x_252, 2, x_152);
x_253 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_253, 0, x_244);
lean_ctor_set(x_253, 1, x_245);
lean_ctor_set(x_253, 2, x_252);
lean_ctor_set(x_253, 3, x_246);
lean_ctor_set(x_253, 4, x_247);
lean_ctor_set(x_253, 5, x_248);
lean_ctor_set(x_232, 0, x_253);
x_33 = x_213;
x_34 = x_232;
goto block_49;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_254 = lean_ctor_get(x_232, 1);
x_255 = lean_ctor_get(x_232, 2);
x_256 = lean_ctor_get(x_232, 3);
x_257 = lean_ctor_get(x_232, 4);
x_258 = lean_ctor_get(x_232, 5);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_232);
x_259 = lean_ctor_get(x_233, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_233, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_233, 3);
lean_inc(x_261);
x_262 = lean_ctor_get(x_233, 4);
lean_inc(x_262);
x_263 = lean_ctor_get(x_233, 5);
lean_inc(x_263);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 lean_ctor_release(x_233, 3);
 lean_ctor_release(x_233, 4);
 lean_ctor_release(x_233, 5);
 x_264 = x_233;
} else {
 lean_dec_ref(x_233);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_234, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_234, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 x_267 = x_234;
} else {
 lean_dec_ref(x_234);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 3, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
lean_ctor_set(x_268, 2, x_152);
if (lean_is_scalar(x_264)) {
 x_269 = lean_alloc_ctor(0, 6, 0);
} else {
 x_269 = x_264;
}
lean_ctor_set(x_269, 0, x_259);
lean_ctor_set(x_269, 1, x_260);
lean_ctor_set(x_269, 2, x_268);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set(x_269, 4, x_262);
lean_ctor_set(x_269, 5, x_263);
x_270 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_254);
lean_ctor_set(x_270, 2, x_255);
lean_ctor_set(x_270, 3, x_256);
lean_ctor_set(x_270, 4, x_257);
lean_ctor_set(x_270, 5, x_258);
x_33 = x_213;
x_34 = x_270;
goto block_49;
}
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_211);
lean_dec(x_208);
x_271 = lean_ctor_get(x_216, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_216, 1);
lean_inc(x_272);
lean_dec(x_216);
x_153 = x_271;
x_154 = x_272;
goto block_193;
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_211);
lean_dec(x_208);
x_273 = lean_ctor_get(x_214, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_214, 1);
lean_inc(x_274);
lean_dec(x_214);
x_153 = x_273;
x_154 = x_274;
goto block_193;
}
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_208);
x_275 = lean_ctor_get(x_210, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_210, 1);
lean_inc(x_276);
lean_dec(x_210);
x_153 = x_275;
x_154 = x_276;
goto block_193;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; 
x_277 = lean_ctor_get(x_195, 0);
lean_inc(x_277);
lean_dec(x_195);
x_278 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_65);
lean_ctor_set(x_278, 2, x_66);
x_279 = lean_ctor_get(x_2, 0);
x_280 = lean_ctor_get(x_2, 1);
x_281 = lean_box(0);
x_282 = 1;
lean_inc(x_280);
lean_inc(x_279);
x_283 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_283, 0, x_278);
lean_ctor_set(x_283, 1, x_279);
lean_ctor_set(x_283, 2, x_280);
lean_ctor_set(x_283, 3, x_6);
lean_ctor_set(x_283, 4, x_197);
lean_ctor_set(x_283, 5, x_198);
lean_ctor_set(x_283, 6, x_199);
lean_ctor_set(x_283, 7, x_281);
lean_ctor_set(x_283, 8, x_200);
lean_ctor_set_uint8(x_283, sizeof(void*)*9, x_282);
x_284 = 0;
lean_inc(x_283);
x_285 = l_Lean_Elab_Term_elabTerm(x_15, x_5, x_284, x_283, x_196);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_box(0);
lean_inc(x_283);
x_289 = l___private_Init_Lean_Elab_Term_18__synthesizeSyntheticMVarsAux___main(x_284, x_288, x_283, x_287);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
lean_inc(x_283);
lean_inc(x_286);
x_291 = l_Lean_Elab_Term_inferType(x_1, x_286, x_283, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
lean_inc(x_283);
x_294 = l_Lean_Elab_Term_instantiateMVars(x_1, x_286, x_283, x_293);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
lean_inc(x_283);
x_297 = l_Lean_Elab_Term_instantiateMVars(x_1, x_292, x_283, x_296);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_300, 0, x_295);
x_301 = l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__8;
x_302 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_303, 0, x_298);
x_304 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = 0;
x_306 = l_Lean_Elab_log___at___private_Init_Lean_Elab_Term_17__reportStuckSyntheticMVars___spec__1(x_1, x_305, x_304, x_283, x_299);
lean_dec(x_283);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_308, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_307, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_307, 3);
lean_inc(x_312);
x_313 = lean_ctor_get(x_307, 4);
lean_inc(x_313);
x_314 = lean_ctor_get(x_307, 5);
lean_inc(x_314);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 lean_ctor_release(x_307, 2);
 lean_ctor_release(x_307, 3);
 lean_ctor_release(x_307, 4);
 lean_ctor_release(x_307, 5);
 x_315 = x_307;
} else {
 lean_dec_ref(x_307);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_308, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_308, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_308, 3);
lean_inc(x_318);
x_319 = lean_ctor_get(x_308, 4);
lean_inc(x_319);
x_320 = lean_ctor_get(x_308, 5);
lean_inc(x_320);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 lean_ctor_release(x_308, 2);
 lean_ctor_release(x_308, 3);
 lean_ctor_release(x_308, 4);
 lean_ctor_release(x_308, 5);
 x_321 = x_308;
} else {
 lean_dec_ref(x_308);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_309, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_309, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 lean_ctor_release(x_309, 2);
 x_324 = x_309;
} else {
 lean_dec_ref(x_309);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(0, 3, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
lean_ctor_set(x_325, 2, x_152);
if (lean_is_scalar(x_321)) {
 x_326 = lean_alloc_ctor(0, 6, 0);
} else {
 x_326 = x_321;
}
lean_ctor_set(x_326, 0, x_316);
lean_ctor_set(x_326, 1, x_317);
lean_ctor_set(x_326, 2, x_325);
lean_ctor_set(x_326, 3, x_318);
lean_ctor_set(x_326, 4, x_319);
lean_ctor_set(x_326, 5, x_320);
if (lean_is_scalar(x_315)) {
 x_327 = lean_alloc_ctor(0, 6, 0);
} else {
 x_327 = x_315;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_310);
lean_ctor_set(x_327, 2, x_311);
lean_ctor_set(x_327, 3, x_312);
lean_ctor_set(x_327, 4, x_313);
lean_ctor_set(x_327, 5, x_314);
x_33 = x_288;
x_34 = x_327;
goto block_49;
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_286);
lean_dec(x_283);
x_328 = lean_ctor_get(x_291, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_291, 1);
lean_inc(x_329);
lean_dec(x_291);
x_153 = x_328;
x_154 = x_329;
goto block_193;
}
}
else
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_286);
lean_dec(x_283);
x_330 = lean_ctor_get(x_289, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_289, 1);
lean_inc(x_331);
lean_dec(x_289);
x_153 = x_330;
x_154 = x_331;
goto block_193;
}
}
else
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_283);
x_332 = lean_ctor_get(x_285, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_285, 1);
lean_inc(x_333);
lean_dec(x_285);
x_153 = x_332;
x_154 = x_333;
goto block_193;
}
}
block_193:
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 2);
lean_inc(x_156);
x_157 = !lean_is_exclusive(x_154);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_154, 0);
lean_dec(x_158);
x_159 = !lean_is_exclusive(x_155);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_155, 2);
lean_dec(x_160);
x_161 = !lean_is_exclusive(x_156);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_156, 2);
lean_dec(x_162);
lean_ctor_set(x_156, 2, x_152);
x_16 = x_153;
x_17 = x_154;
goto block_32;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_156, 0);
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_152);
lean_ctor_set(x_155, 2, x_165);
x_16 = x_153;
x_17 = x_154;
goto block_32;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_166 = lean_ctor_get(x_155, 0);
x_167 = lean_ctor_get(x_155, 1);
x_168 = lean_ctor_get(x_155, 3);
x_169 = lean_ctor_get(x_155, 4);
x_170 = lean_ctor_get(x_155, 5);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_155);
x_171 = lean_ctor_get(x_156, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_156, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 x_173 = x_156;
} else {
 lean_dec_ref(x_156);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 3, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
lean_ctor_set(x_174, 2, x_152);
x_175 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_175, 0, x_166);
lean_ctor_set(x_175, 1, x_167);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_168);
lean_ctor_set(x_175, 4, x_169);
lean_ctor_set(x_175, 5, x_170);
lean_ctor_set(x_154, 0, x_175);
x_16 = x_153;
x_17 = x_154;
goto block_32;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_176 = lean_ctor_get(x_154, 1);
x_177 = lean_ctor_get(x_154, 2);
x_178 = lean_ctor_get(x_154, 3);
x_179 = lean_ctor_get(x_154, 4);
x_180 = lean_ctor_get(x_154, 5);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_154);
x_181 = lean_ctor_get(x_155, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_155, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_155, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_155, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_155, 5);
lean_inc(x_185);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 lean_ctor_release(x_155, 5);
 x_186 = x_155;
} else {
 lean_dec_ref(x_155);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_156, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_156, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 x_189 = x_156;
} else {
 lean_dec_ref(x_156);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 3, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
lean_ctor_set(x_190, 2, x_152);
if (lean_is_scalar(x_186)) {
 x_191 = lean_alloc_ctor(0, 6, 0);
} else {
 x_191 = x_186;
}
lean_ctor_set(x_191, 0, x_181);
lean_ctor_set(x_191, 1, x_182);
lean_ctor_set(x_191, 2, x_190);
lean_ctor_set(x_191, 3, x_183);
lean_ctor_set(x_191, 4, x_184);
lean_ctor_set(x_191, 5, x_185);
x_192 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_176);
lean_ctor_set(x_192, 2, x_177);
lean_ctor_set(x_192, 3, x_178);
lean_ctor_set(x_192, 4, x_179);
lean_ctor_set(x_192, 5, x_180);
x_16 = x_153;
x_17 = x_192;
goto block_32;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_57);
lean_dec(x_15);
lean_dec(x_6);
x_334 = lean_ctor_get(x_61, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_61, 1);
lean_inc(x_335);
lean_dec(x_61);
x_16 = x_334;
x_17 = x_335;
goto block_32;
}
block_32:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = l_Lean_Elab_Term_getTraceState___rarg(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_23 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__1(x_3, x_21, x_22, x_8, x_20);
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_setTraceState(x_11, x_8, x_24);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_16);
x_28 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_30);
return x_31;
}
}
block_49:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = l_Lean_Elab_Term_getTraceState___rarg(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_40 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__2(x_3, x_38, x_39, x_8, x_37);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Elab_Term_setTraceState(x_11, x_8, x_41);
lean_dec(x_8);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_33);
x_45 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg(x_3, x_47);
return x_48;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabCheck___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabCheck(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___closed__2;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___boxed), 3, 0);
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
lean_object* initialize_Init_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object*);
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
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
l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Command_mkCommandElabAttribute___spec__4___closed__2);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__1 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__1);
l_Lean_Elab_Command_mkCommandElabAttribute___closed__2 = _init_l_Lean_Elab_Command_mkCommandElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttribute___closed__2);
l_Lean_Elab_Command_commandElabAttribute___closed__1 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__1);
l_Lean_Elab_Command_commandElabAttribute___closed__2 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__2);
l_Lean_Elab_Command_commandElabAttribute___closed__3 = _init_l_Lean_Elab_Command_commandElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute___closed__3);
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
l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_4__toCommandResult___rarg___closed__1);
l___private_Init_Lean_Elab_Command_6__addScopes___main___closed__1 = _init_l___private_Init_Lean_Elab_Command_6__addScopes___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Command_6__addScopes___main___closed__1);
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
l_Lean_Elab_Command_addUniverse___closed__1 = _init_l_Lean_Elab_Command_addUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_addUniverse___closed__1);
l_Lean_Elab_Command_addUniverse___closed__2 = _init_l_Lean_Elab_Command_addUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_addUniverse___closed__2);
l_Lean_Elab_Command_addUniverse___closed__3 = _init_l_Lean_Elab_Command_addUniverse___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_addUniverse___closed__3);
l_Lean_Elab_Command_addUniverse___closed__4 = _init_l_Lean_Elab_Command_addUniverse___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_addUniverse___closed__4);
l_Lean_Elab_Command_addUniverse___closed__5 = _init_l_Lean_Elab_Command_addUniverse___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_addUniverse___closed__5);
l_Lean_Elab_Command_addUniverse___closed__6 = _init_l_Lean_Elab_Command_addUniverse___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_addUniverse___closed__6);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
